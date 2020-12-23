%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:02 EST 2020

% Result     : Theorem 1.43s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 280 expanded)
%              Number of leaves         :   28 (  94 expanded)
%              Depth                    :   16
%              Number of atoms          :  510 (1065 expanded)
%              Number of equality atoms :   66 ( 165 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f281,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f102,f107,f112,f128,f132,f136,f228,f238,f254,f258,f264,f280])).

fof(f280,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_3
    | spl4_11
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f277])).

fof(f277,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | spl4_3
    | spl4_11
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f96,f101,f106,f237,f253,f145])).

fof(f145,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(resolution,[],[f80,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | r2_hidden(X0,X1)
      | X0 = X1 ) ),
    inference(definition_unfolding,[],[f62,f76])).

fof(f76,plain,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).

fof(f62,plain,(
    ! [X0,X1] :
      ( X0 = X1
      | r2_hidden(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r2_hidden(X0,k1_ordinal1(X1))
        | ( X0 != X1
          & ~ r2_hidden(X0,X1) ) )
      & ( X0 = X1
        | r2_hidden(X0,X1)
        | ~ r2_hidden(X0,k1_ordinal1(X1)) ) ) ),
    inference(nnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
    <=> ( X0 = X1
        | r2_hidden(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).

fof(f80,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f75,f76])).

fof(f75,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r2_hidden(X0,k1_ordinal1(X1))
              | ~ r1_ordinal1(X0,X1) )
            & ( r1_ordinal1(X0,X1)
              | ~ r2_hidden(X0,k1_ordinal1(X1)) ) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) )
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,k1_ordinal1(X1))
          <=> r1_ordinal1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).

fof(f253,plain,
    ( r1_ordinal1(sK0,sK1)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f251])).

fof(f251,plain,
    ( spl4_12
  <=> r1_ordinal1(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f237,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_11 ),
    inference(avatar_component_clause,[],[f235])).

fof(f235,plain,
    ( spl4_11
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f106,plain,
    ( sK0 != sK1
    | spl4_3 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl4_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f101,plain,
    ( v3_ordinal1(sK1)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl4_2
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

% (2330)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% (2330)Refutation not found, incomplete strategy% (2330)------------------------------
% (2330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2330)Termination reason: Refutation not found, incomplete strategy

% (2330)Memory used [KB]: 1663
% (2330)Time elapsed: 0.143 s
% (2330)------------------------------
% (2330)------------------------------
% (2325)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% (2340)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% (2337)Refutation not found, incomplete strategy% (2337)------------------------------
% (2337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (2337)Termination reason: Refutation not found, incomplete strategy

% (2337)Memory used [KB]: 10618
% (2337)Time elapsed: 0.123 s
% (2337)------------------------------
% (2337)------------------------------
% (2339)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% (2339)Refutation not found, incomplete strategy% (2339)------------------------------
% (2339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
fof(f96,plain,
    ( v3_ordinal1(sK0)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl4_1
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f264,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_3
    | spl4_9
    | spl4_12 ),
    inference(avatar_contradiction_clause,[],[f262])).

fof(f262,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | spl4_3
    | spl4_9
    | spl4_12 ),
    inference(unit_resulting_resolution,[],[f101,f96,f106,f227,f252,f165])).

fof(f165,plain,(
    ! [X6,X5] :
      ( r2_hidden(X5,X6)
      | ~ v3_ordinal1(X6)
      | r1_ordinal1(X6,X5)
      | X5 = X6
      | ~ v3_ordinal1(X5) ) ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,(
    ! [X6,X5] :
      ( ~ v3_ordinal1(X5)
      | ~ v3_ordinal1(X6)
      | r1_ordinal1(X6,X5)
      | X5 = X6
      | r2_hidden(X5,X6)
      | ~ v3_ordinal1(X6)
      | ~ v3_ordinal1(X5) ) ),
    inference(resolution,[],[f149,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( r2_hidden(X1,X0)
      | X0 = X1
      | r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f149,plain,(
    ! [X4,X3] :
      ( ~ r2_hidden(X3,X4)
      | ~ v3_ordinal1(X4)
      | ~ v3_ordinal1(X3)
      | r1_ordinal1(X3,X4) ) ),
    inference(resolution,[],[f81,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | ~ r2_hidden(X0,X1) ) ),
    inference(definition_unfolding,[],[f63,f76])).

fof(f63,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,k1_ordinal1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1)))
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(definition_unfolding,[],[f74,f76])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X0,X1)
      | ~ r2_hidden(X0,k1_ordinal1(X1))
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f252,plain,
    ( ~ r1_ordinal1(sK0,sK1)
    | spl4_12 ),
    inference(avatar_component_clause,[],[f251])).

fof(f227,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl4_9 ),
    inference(avatar_component_clause,[],[f225])).

fof(f225,plain,
    ( spl4_9
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f258,plain,
    ( ~ spl4_1
    | ~ spl4_2
    | spl4_10
    | ~ spl4_12 ),
    inference(avatar_contradiction_clause,[],[f255])).

fof(f255,plain,
    ( $false
    | ~ spl4_1
    | ~ spl4_2
    | spl4_10
    | ~ spl4_12 ),
    inference(unit_resulting_resolution,[],[f96,f101,f233,f253,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ r1_ordinal1(X0,X1)
      | r1_tarski(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( r1_ordinal1(X0,X1)
          | ~ r1_tarski(X0,X1) )
        & ( r1_tarski(X0,X1)
          | ~ r1_ordinal1(X0,X1) ) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).

fof(f233,plain,
    ( ~ r1_tarski(sK0,sK1)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f231])).

fof(f231,plain,
    ( spl4_10
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f254,plain,
    ( spl4_12
    | ~ spl4_1
    | ~ spl4_2
    | spl4_3
    | spl4_8 ),
    inference(avatar_split_clause,[],[f229,f221,f104,f99,f94,f251])).

fof(f221,plain,
    ( spl4_8
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f229,plain,
    ( sK0 = sK1
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | r1_ordinal1(sK0,sK1)
    | spl4_8 ),
    inference(resolution,[],[f223,f190])).

fof(f190,plain,(
    ! [X2,X3] :
      ( r1_tarski(X3,X2)
      | X2 = X3
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(X2)
      | r1_ordinal1(X2,X3) ) ),
    inference(duplicate_literal_removal,[],[f187])).

fof(f187,plain,(
    ! [X2,X3] :
      ( r1_ordinal1(X2,X3)
      | X2 = X3
      | ~ v3_ordinal1(X3)
      | ~ v3_ordinal1(X2)
      | r1_tarski(X3,X2)
      | ~ v3_ordinal1(X2)
      | ~ v3_ordinal1(X3) ) ),
    inference(resolution,[],[f185,f72])).

fof(f185,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | X0 = X1
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(duplicate_literal_removal,[],[f179])).

fof(f179,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | r1_ordinal1(X0,X1)
      | X0 = X1
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X1,X0) ) ),
    inference(resolution,[],[f165,f149])).

fof(f223,plain,
    ( ~ r1_tarski(sK1,sK0)
    | spl4_8 ),
    inference(avatar_component_clause,[],[f221])).

fof(f238,plain,
    ( ~ spl4_10
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_11
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f219,f125,f235,f99,f94,f231])).

% (2322)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
fof(f125,plain,
    ( spl4_7
  <=> r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f219,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ v3_ordinal1(sK0)
    | ~ r1_tarski(sK0,sK1)
    | ~ spl4_7 ),
    inference(resolution,[],[f203,f127])).

fof(f127,plain,
    ( r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f125])).

fof(f203,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | ~ r1_tarski(X1,X0) ) ),
    inference(superposition,[],[f198,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

fof(f198,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(global_subsumption,[],[f60,f59,f197])).

fof(f197,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ v2_wellord1(k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(duplicate_literal_removal,[],[f196])).

fof(f196,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,X0)
      | ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ v2_wellord1(k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(forward_demodulation,[],[f194,f92])).

fof(f92,plain,(
    ! [X0] : k3_relat_1(k1_wellord2(X0)) = X0 ),
    inference(global_subsumption,[],[f60,f89])).

fof(f89,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ( ( ~ r1_tarski(sK2(X0,X1),sK3(X0,X1))
              | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
            & ( r1_tarski(sK2(X0,X1),sK3(X0,X1))
              | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
            & r2_hidden(sK3(X0,X1),X0)
            & r2_hidden(sK2(X0,X1),X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f45,f46])).

% (2333)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
fof(f46,plain,(
    ! [X1,X0] :
      ( ? [X2,X3] :
          ( ( ~ r1_tarski(X2,X3)
            | ~ r2_hidden(k4_tarski(X2,X3),X1) )
          & ( r1_tarski(X2,X3)
            | r2_hidden(k4_tarski(X2,X3),X1) )
          & r2_hidden(X3,X0)
          & r2_hidden(X2,X0) )
     => ( ( ~ r1_tarski(sK2(X0,X1),sK3(X0,X1))
          | ~ r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & ( r1_tarski(sK2(X0,X1),sK3(X0,X1))
          | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1) )
        & r2_hidden(sK3(X0,X1),X0)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X4,X5] :
                ( ( ( r2_hidden(k4_tarski(X4,X5),X1)
                    | ~ r1_tarski(X4,X5) )
                  & ( r1_tarski(X4,X5)
                    | ~ r2_hidden(k4_tarski(X4,X5),X1) ) )
                | ~ r2_hidden(X5,X0)
                | ~ r2_hidden(X4,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(rectify,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( ( k1_wellord2(X0) = X1
          | ? [X2,X3] :
              ( ( ~ r1_tarski(X2,X3)
                | ~ r2_hidden(k4_tarski(X2,X3),X1) )
              & ( r1_tarski(X2,X3)
                | r2_hidden(k4_tarski(X2,X3),X1) )
              & r2_hidden(X3,X0)
              & r2_hidden(X2,X0) )
          | k3_relat_1(X1) != X0 )
        & ( ( ! [X2,X3] :
                ( ( ( r2_hidden(k4_tarski(X2,X3),X1)
                    | ~ r1_tarski(X2,X3) )
                  & ( r1_tarski(X2,X3)
                    | ~ r2_hidden(k4_tarski(X2,X3),X1) ) )
                | ~ r2_hidden(X3,X0)
                | ~ r2_hidden(X2,X0) )
            & k3_relat_1(X1) = X0 )
          | k1_wellord2(X0) != X1 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).

fof(f194,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1))
      | ~ r2_hidden(X1,k3_relat_1(k1_wellord2(X0)))
      | ~ v2_wellord1(k1_wellord2(X0))
      | ~ v1_relat_1(k1_wellord2(X0))
      | ~ r2_hidden(X1,X0)
      | ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1) ) ),
    inference(superposition,[],[f56,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( k1_wellord1(k1_wellord2(X1),X0) = X0
      | ~ r2_hidden(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

fof(f59,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

% (2334)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
fof(f30,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

fof(f60,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f228,plain,
    ( ~ spl4_8
    | ~ spl4_2
    | ~ spl4_1
    | ~ spl4_9
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f218,f109,f225,f94,f99,f221])).

fof(f109,plain,
    ( spl4_4
  <=> r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f218,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ v3_ordinal1(sK1)
    | ~ r1_tarski(sK1,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f203,f111])).

fof(f111,plain,
    ( r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f109])).

fof(f136,plain,(
    spl4_6 ),
    inference(avatar_contradiction_clause,[],[f133])).

fof(f133,plain,
    ( $false
    | spl4_6 ),
    inference(unit_resulting_resolution,[],[f60,f123])).

fof(f123,plain,
    ( ~ v1_relat_1(k1_wellord2(sK1))
    | spl4_6 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl4_6
  <=> v1_relat_1(k1_wellord2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f132,plain,(
    spl4_5 ),
    inference(avatar_contradiction_clause,[],[f129])).

fof(f129,plain,
    ( $false
    | spl4_5 ),
    inference(unit_resulting_resolution,[],[f60,f119])).

fof(f119,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | spl4_5 ),
    inference(avatar_component_clause,[],[f117])).

fof(f117,plain,
    ( spl4_5
  <=> v1_relat_1(k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f128,plain,
    ( ~ spl4_5
    | ~ spl4_6
    | spl4_7
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f115,f109,f125,f121,f117])).

fof(f115,plain,
    ( r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | ~ v1_relat_1(k1_wellord2(sK1))
    | ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f55,f111])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ r4_wellord1(X0,X1)
      | r4_wellord1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

% (2332)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(f112,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f52,f109])).

fof(f52,plain,(
    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,
    ( sK0 != sK1
    & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    & v3_ordinal1(sK1)
    & v3_ordinal1(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( X0 != X1
            & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
            & v3_ordinal1(X1) )
        & v3_ordinal1(X0) )
   => ( ? [X1] :
          ( sK0 != X1
          & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( sK0 != X1
        & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1))
        & v3_ordinal1(X1) )
   => ( sK0 != sK1
      & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
      & v3_ordinal1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

fof(f107,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f53,f104])).

fof(f53,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f40])).

fof(f102,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f51,f99])).

fof(f51,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f40])).

fof(f97,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f50,f94])).

fof(f50,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f40])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 18:38:22 EST 2020
% 0.14/0.35  % CPUTime    : 
% 1.22/0.53  % (2314)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.22/0.53  % (2315)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.22/0.53  % (2314)Refutation not found, incomplete strategy% (2314)------------------------------
% 1.22/0.53  % (2314)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.22/0.53  % (2314)Termination reason: Refutation not found, incomplete strategy
% 1.22/0.53  
% 1.22/0.53  % (2314)Memory used [KB]: 1663
% 1.22/0.53  % (2314)Time elapsed: 0.122 s
% 1.22/0.53  % (2314)------------------------------
% 1.22/0.53  % (2314)------------------------------
% 1.22/0.53  % (2336)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.22/0.53  % (2323)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 1.22/0.53  % (2328)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 1.22/0.54  % (2321)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.22/0.54  % (2320)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.22/0.54  % (2317)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 1.43/0.55  % (2318)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 1.43/0.55  % (2324)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.43/0.55  % (2319)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.43/0.55  % (2313)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 1.43/0.55  % (2329)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.43/0.55  % (2337)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 1.43/0.55  % (2329)Refutation not found, incomplete strategy% (2329)------------------------------
% 1.43/0.55  % (2329)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.55  % (2329)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.55  
% 1.43/0.55  % (2329)Memory used [KB]: 10618
% 1.43/0.55  % (2329)Time elapsed: 0.144 s
% 1.43/0.55  % (2329)------------------------------
% 1.43/0.55  % (2329)------------------------------
% 1.43/0.55  % (2336)Refutation found. Thanks to Tanya!
% 1.43/0.55  % SZS status Theorem for theBenchmark
% 1.43/0.55  % SZS output start Proof for theBenchmark
% 1.43/0.55  fof(f281,plain,(
% 1.43/0.55    $false),
% 1.43/0.55    inference(avatar_sat_refutation,[],[f97,f102,f107,f112,f128,f132,f136,f228,f238,f254,f258,f264,f280])).
% 1.43/0.55  fof(f280,plain,(
% 1.43/0.55    ~spl4_1 | ~spl4_2 | spl4_3 | spl4_11 | ~spl4_12),
% 1.43/0.55    inference(avatar_contradiction_clause,[],[f277])).
% 1.43/0.55  fof(f277,plain,(
% 1.43/0.55    $false | (~spl4_1 | ~spl4_2 | spl4_3 | spl4_11 | ~spl4_12)),
% 1.43/0.55    inference(unit_resulting_resolution,[],[f96,f101,f106,f237,f253,f145])).
% 1.43/0.55  fof(f145,plain,(
% 1.43/0.55    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | r2_hidden(X0,X1) | X0 = X1) )),
% 1.43/0.55    inference(resolution,[],[f80,f79])).
% 1.43/0.55  fof(f79,plain,(
% 1.43/0.55    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | r2_hidden(X0,X1) | X0 = X1) )),
% 1.43/0.55    inference(definition_unfolding,[],[f62,f76])).
% 1.43/0.55  fof(f76,plain,(
% 1.43/0.55    ( ! [X0] : (k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))) )),
% 1.43/0.55    inference(cnf_transformation,[],[f4])).
% 1.43/0.55  fof(f4,axiom,(
% 1.43/0.55    ! [X0] : k1_ordinal1(X0) = k2_xboole_0(X0,k1_tarski(X0))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_ordinal1)).
% 1.43/0.55  fof(f62,plain,(
% 1.43/0.55    ( ! [X0,X1] : (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))) )),
% 1.43/0.55    inference(cnf_transformation,[],[f42])).
% 1.43/0.55  fof(f42,plain,(
% 1.43/0.55    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & (X0 = X1 | r2_hidden(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 1.43/0.55    inference(flattening,[],[f41])).
% 1.43/0.55  fof(f41,plain,(
% 1.43/0.55    ! [X0,X1] : ((r2_hidden(X0,k1_ordinal1(X1)) | (X0 != X1 & ~r2_hidden(X0,X1))) & ((X0 = X1 | r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_ordinal1(X1))))),
% 1.43/0.55    inference(nnf_transformation,[],[f6])).
% 1.43/0.55  fof(f6,axiom,(
% 1.43/0.55    ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) <=> (X0 = X1 | r2_hidden(X0,X1)))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_ordinal1)).
% 1.43/0.55  fof(f80,plain,(
% 1.43/0.55    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.43/0.55    inference(definition_unfolding,[],[f75,f76])).
% 1.43/0.55  fof(f75,plain,(
% 1.43/0.55    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.43/0.55    inference(cnf_transformation,[],[f49])).
% 1.43/0.55  fof(f49,plain,(
% 1.43/0.55    ! [X0] : (! [X1] : (((r2_hidden(X0,k1_ordinal1(X1)) | ~r1_ordinal1(X0,X1)) & (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)))) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.43/0.55    inference(nnf_transformation,[],[f37])).
% 1.43/0.55  fof(f37,plain,(
% 1.43/0.55    ! [X0] : (! [X1] : ((r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.43/0.55    inference(ennf_transformation,[],[f9])).
% 1.43/0.55  fof(f9,axiom,(
% 1.43/0.55    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,k1_ordinal1(X1)) <=> r1_ordinal1(X0,X1))))),
% 1.43/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_ordinal1)).
% 1.43/0.55  fof(f253,plain,(
% 1.43/0.55    r1_ordinal1(sK0,sK1) | ~spl4_12),
% 1.43/0.55    inference(avatar_component_clause,[],[f251])).
% 1.43/0.55  fof(f251,plain,(
% 1.43/0.55    spl4_12 <=> r1_ordinal1(sK0,sK1)),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.43/0.55  fof(f237,plain,(
% 1.43/0.55    ~r2_hidden(sK0,sK1) | spl4_11),
% 1.43/0.55    inference(avatar_component_clause,[],[f235])).
% 1.43/0.55  fof(f235,plain,(
% 1.43/0.55    spl4_11 <=> r2_hidden(sK0,sK1)),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.43/0.55  fof(f106,plain,(
% 1.43/0.55    sK0 != sK1 | spl4_3),
% 1.43/0.55    inference(avatar_component_clause,[],[f104])).
% 1.43/0.55  fof(f104,plain,(
% 1.43/0.55    spl4_3 <=> sK0 = sK1),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.43/0.55  fof(f101,plain,(
% 1.43/0.55    v3_ordinal1(sK1) | ~spl4_2),
% 1.43/0.55    inference(avatar_component_clause,[],[f99])).
% 1.43/0.55  fof(f99,plain,(
% 1.43/0.55    spl4_2 <=> v3_ordinal1(sK1)),
% 1.43/0.55    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.43/0.55  % (2330)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 1.43/0.56  % (2330)Refutation not found, incomplete strategy% (2330)------------------------------
% 1.43/0.56  % (2330)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (2330)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (2330)Memory used [KB]: 1663
% 1.43/0.56  % (2330)Time elapsed: 0.143 s
% 1.43/0.56  % (2330)------------------------------
% 1.43/0.56  % (2330)------------------------------
% 1.43/0.56  % (2325)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 1.43/0.56  % (2340)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.43/0.56  % (2337)Refutation not found, incomplete strategy% (2337)------------------------------
% 1.43/0.56  % (2337)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (2337)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.56  
% 1.43/0.56  % (2337)Memory used [KB]: 10618
% 1.43/0.56  % (2337)Time elapsed: 0.123 s
% 1.43/0.56  % (2337)------------------------------
% 1.43/0.56  % (2337)------------------------------
% 1.43/0.56  % (2339)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 1.43/0.56  % (2339)Refutation not found, incomplete strategy% (2339)------------------------------
% 1.43/0.56  % (2339)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  fof(f96,plain,(
% 1.43/0.56    v3_ordinal1(sK0) | ~spl4_1),
% 1.43/0.56    inference(avatar_component_clause,[],[f94])).
% 1.43/0.56  fof(f94,plain,(
% 1.43/0.56    spl4_1 <=> v3_ordinal1(sK0)),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.43/0.56  fof(f264,plain,(
% 1.43/0.56    ~spl4_1 | ~spl4_2 | spl4_3 | spl4_9 | spl4_12),
% 1.43/0.56    inference(avatar_contradiction_clause,[],[f262])).
% 1.43/0.56  fof(f262,plain,(
% 1.43/0.56    $false | (~spl4_1 | ~spl4_2 | spl4_3 | spl4_9 | spl4_12)),
% 1.43/0.56    inference(unit_resulting_resolution,[],[f101,f96,f106,f227,f252,f165])).
% 1.43/0.56  fof(f165,plain,(
% 1.43/0.56    ( ! [X6,X5] : (r2_hidden(X5,X6) | ~v3_ordinal1(X6) | r1_ordinal1(X6,X5) | X5 = X6 | ~v3_ordinal1(X5)) )),
% 1.43/0.56    inference(duplicate_literal_removal,[],[f163])).
% 1.43/0.56  fof(f163,plain,(
% 1.43/0.56    ( ! [X6,X5] : (~v3_ordinal1(X5) | ~v3_ordinal1(X6) | r1_ordinal1(X6,X5) | X5 = X6 | r2_hidden(X5,X6) | ~v3_ordinal1(X6) | ~v3_ordinal1(X5)) )),
% 1.43/0.56    inference(resolution,[],[f149,f54])).
% 1.43/0.56  fof(f54,plain,(
% 1.43/0.56    ( ! [X0,X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f22])).
% 1.43/0.56  fof(f22,plain,(
% 1.43/0.56    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.43/0.56    inference(flattening,[],[f21])).
% 1.43/0.56  fof(f21,plain,(
% 1.43/0.56    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.43/0.56    inference(ennf_transformation,[],[f8])).
% 1.43/0.56  fof(f8,axiom,(
% 1.43/0.56    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_ordinal1)).
% 1.43/0.56  fof(f149,plain,(
% 1.43/0.56    ( ! [X4,X3] : (~r2_hidden(X3,X4) | ~v3_ordinal1(X4) | ~v3_ordinal1(X3) | r1_ordinal1(X3,X4)) )),
% 1.43/0.56    inference(resolution,[],[f81,f78])).
% 1.43/0.56  fof(f78,plain,(
% 1.43/0.56    ( ! [X0,X1] : (r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | ~r2_hidden(X0,X1)) )),
% 1.43/0.56    inference(definition_unfolding,[],[f63,f76])).
% 1.43/0.56  fof(f63,plain,(
% 1.43/0.56    ( ! [X0,X1] : (r2_hidden(X0,k1_ordinal1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f42])).
% 1.43/0.56  fof(f81,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~r2_hidden(X0,k2_xboole_0(X1,k1_tarski(X1))) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.43/0.56    inference(definition_unfolding,[],[f74,f76])).
% 1.43/0.56  fof(f74,plain,(
% 1.43/0.56    ( ! [X0,X1] : (r1_ordinal1(X0,X1) | ~r2_hidden(X0,k1_ordinal1(X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f49])).
% 1.43/0.56  fof(f252,plain,(
% 1.43/0.56    ~r1_ordinal1(sK0,sK1) | spl4_12),
% 1.43/0.56    inference(avatar_component_clause,[],[f251])).
% 1.43/0.56  fof(f227,plain,(
% 1.43/0.56    ~r2_hidden(sK1,sK0) | spl4_9),
% 1.43/0.56    inference(avatar_component_clause,[],[f225])).
% 1.43/0.56  fof(f225,plain,(
% 1.43/0.56    spl4_9 <=> r2_hidden(sK1,sK0)),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.43/0.56  fof(f258,plain,(
% 1.43/0.56    ~spl4_1 | ~spl4_2 | spl4_10 | ~spl4_12),
% 1.43/0.56    inference(avatar_contradiction_clause,[],[f255])).
% 1.43/0.56  fof(f255,plain,(
% 1.43/0.56    $false | (~spl4_1 | ~spl4_2 | spl4_10 | ~spl4_12)),
% 1.43/0.56    inference(unit_resulting_resolution,[],[f96,f101,f233,f253,f72])).
% 1.43/0.56  fof(f72,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~r1_ordinal1(X0,X1) | r1_tarski(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f48])).
% 1.43/0.56  fof(f48,plain,(
% 1.43/0.56    ! [X0,X1] : (((r1_ordinal1(X0,X1) | ~r1_tarski(X0,X1)) & (r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1))) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.43/0.56    inference(nnf_transformation,[],[f36])).
% 1.43/0.56  fof(f36,plain,(
% 1.43/0.56    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.43/0.56    inference(flattening,[],[f35])).
% 1.43/0.56  fof(f35,plain,(
% 1.43/0.56    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.43/0.56    inference(ennf_transformation,[],[f5])).
% 1.43/0.56  fof(f5,axiom,(
% 1.43/0.56    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.43/0.56  fof(f233,plain,(
% 1.43/0.56    ~r1_tarski(sK0,sK1) | spl4_10),
% 1.43/0.56    inference(avatar_component_clause,[],[f231])).
% 1.43/0.56  fof(f231,plain,(
% 1.43/0.56    spl4_10 <=> r1_tarski(sK0,sK1)),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.43/0.56  fof(f254,plain,(
% 1.43/0.56    spl4_12 | ~spl4_1 | ~spl4_2 | spl4_3 | spl4_8),
% 1.43/0.56    inference(avatar_split_clause,[],[f229,f221,f104,f99,f94,f251])).
% 1.43/0.56  fof(f221,plain,(
% 1.43/0.56    spl4_8 <=> r1_tarski(sK1,sK0)),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.43/0.56  fof(f229,plain,(
% 1.43/0.56    sK0 = sK1 | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | r1_ordinal1(sK0,sK1) | spl4_8),
% 1.43/0.56    inference(resolution,[],[f223,f190])).
% 1.43/0.56  fof(f190,plain,(
% 1.43/0.56    ( ! [X2,X3] : (r1_tarski(X3,X2) | X2 = X3 | ~v3_ordinal1(X3) | ~v3_ordinal1(X2) | r1_ordinal1(X2,X3)) )),
% 1.43/0.56    inference(duplicate_literal_removal,[],[f187])).
% 1.43/0.56  fof(f187,plain,(
% 1.43/0.56    ( ! [X2,X3] : (r1_ordinal1(X2,X3) | X2 = X3 | ~v3_ordinal1(X3) | ~v3_ordinal1(X2) | r1_tarski(X3,X2) | ~v3_ordinal1(X2) | ~v3_ordinal1(X3)) )),
% 1.43/0.56    inference(resolution,[],[f185,f72])).
% 1.43/0.56  fof(f185,plain,(
% 1.43/0.56    ( ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | X0 = X1 | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.43/0.56    inference(duplicate_literal_removal,[],[f179])).
% 1.43/0.56  fof(f179,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~v3_ordinal1(X0) | r1_ordinal1(X0,X1) | X0 = X1 | ~v3_ordinal1(X1) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_ordinal1(X1,X0)) )),
% 1.43/0.56    inference(resolution,[],[f165,f149])).
% 1.43/0.56  fof(f223,plain,(
% 1.43/0.56    ~r1_tarski(sK1,sK0) | spl4_8),
% 1.43/0.56    inference(avatar_component_clause,[],[f221])).
% 1.43/0.56  fof(f238,plain,(
% 1.43/0.56    ~spl4_10 | ~spl4_1 | ~spl4_2 | ~spl4_11 | ~spl4_7),
% 1.43/0.56    inference(avatar_split_clause,[],[f219,f125,f235,f99,f94,f231])).
% 1.43/0.56  % (2322)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.43/0.56  fof(f125,plain,(
% 1.43/0.56    spl4_7 <=> r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.43/0.56  fof(f219,plain,(
% 1.43/0.56    ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | ~v3_ordinal1(sK0) | ~r1_tarski(sK0,sK1) | ~spl4_7),
% 1.43/0.56    inference(resolution,[],[f203,f127])).
% 1.43/0.56  fof(f127,plain,(
% 1.43/0.56    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | ~spl4_7),
% 1.43/0.56    inference(avatar_component_clause,[],[f125])).
% 1.43/0.56  fof(f203,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1) | ~r1_tarski(X1,X0)) )),
% 1.43/0.56    inference(superposition,[],[f198,f57])).
% 1.43/0.56  fof(f57,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f27])).
% 1.43/0.56  fof(f27,plain,(
% 1.43/0.56    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 1.43/0.56    inference(ennf_transformation,[],[f16])).
% 1.43/0.56  fof(f16,axiom,(
% 1.43/0.56    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).
% 1.43/0.56  fof(f198,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 1.43/0.56    inference(global_subsumption,[],[f60,f59,f197])).
% 1.43/0.56  fof(f197,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) | ~v2_wellord1(k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0)) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 1.43/0.56    inference(duplicate_literal_removal,[],[f196])).
% 1.43/0.56  fof(f196,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~r2_hidden(X1,X0) | ~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) | ~v2_wellord1(k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0)) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 1.43/0.56    inference(forward_demodulation,[],[f194,f92])).
% 1.43/0.56  fof(f92,plain,(
% 1.43/0.56    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0) )),
% 1.43/0.56    inference(global_subsumption,[],[f60,f89])).
% 1.43/0.56  fof(f89,plain,(
% 1.43/0.56    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 1.43/0.56    inference(equality_resolution,[],[f65])).
% 1.43/0.56  fof(f65,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1 | ~v1_relat_1(X1)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f47])).
% 1.43/0.56  fof(f47,plain,(
% 1.43/0.56    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ((~r1_tarski(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r1_tarski(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3])],[f45,f46])).
% 1.43/0.56  % (2333)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.43/0.56  fof(f46,plain,(
% 1.43/0.56    ! [X1,X0] : (? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) => ((~r1_tarski(sK2(X0,X1),sK3(X0,X1)) | ~r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & (r1_tarski(sK2(X0,X1),sK3(X0,X1)) | r2_hidden(k4_tarski(sK2(X0,X1),sK3(X0,X1)),X1)) & r2_hidden(sK3(X0,X1),X0) & r2_hidden(sK2(X0,X1),X0)))),
% 1.43/0.56    introduced(choice_axiom,[])).
% 1.43/0.56  fof(f45,plain,(
% 1.43/0.56    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X4,X5] : (((r2_hidden(k4_tarski(X4,X5),X1) | ~r1_tarski(X4,X5)) & (r1_tarski(X4,X5) | ~r2_hidden(k4_tarski(X4,X5),X1))) | ~r2_hidden(X5,X0) | ~r2_hidden(X4,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(rectify,[],[f44])).
% 1.43/0.56  fof(f44,plain,(
% 1.43/0.56    ! [X0,X1] : (((k1_wellord2(X0) = X1 | ? [X2,X3] : ((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1)) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(flattening,[],[f43])).
% 1.43/0.56  fof(f43,plain,(
% 1.43/0.56    ! [X0,X1] : (((k1_wellord2(X0) = X1 | (? [X2,X3] : (((~r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1)) & (r1_tarski(X2,X3) | r2_hidden(k4_tarski(X2,X3),X1))) & r2_hidden(X3,X0) & r2_hidden(X2,X0)) | k3_relat_1(X1) != X0)) & ((! [X2,X3] : (((r2_hidden(k4_tarski(X2,X3),X1) | ~r1_tarski(X2,X3)) & (r1_tarski(X2,X3) | ~r2_hidden(k4_tarski(X2,X3),X1))) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0) | k1_wellord2(X0) != X1)) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(nnf_transformation,[],[f34])).
% 1.43/0.56  fof(f34,plain,(
% 1.43/0.56    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(flattening,[],[f33])).
% 1.43/0.56  fof(f33,plain,(
% 1.43/0.56    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 1.43/0.56    inference(ennf_transformation,[],[f12])).
% 1.43/0.56  fof(f12,axiom,(
% 1.43/0.56    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 1.43/0.56  fof(f194,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~r4_wellord1(k1_wellord2(X0),k2_wellord1(k1_wellord2(X0),X1)) | ~r2_hidden(X1,k3_relat_1(k1_wellord2(X0))) | ~v2_wellord1(k1_wellord2(X0)) | ~v1_relat_1(k1_wellord2(X0)) | ~r2_hidden(X1,X0) | ~v3_ordinal1(X0) | ~v3_ordinal1(X1)) )),
% 1.43/0.56    inference(superposition,[],[f56,f58])).
% 1.43/0.56  fof(f58,plain,(
% 1.43/0.56    ( ! [X0,X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f29])).
% 1.43/0.56  fof(f29,plain,(
% 1.43/0.56    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.43/0.56    inference(flattening,[],[f28])).
% 1.43/0.56  fof(f28,plain,(
% 1.43/0.56    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 1.43/0.56    inference(ennf_transformation,[],[f14])).
% 1.43/0.56  fof(f14,axiom,(
% 1.43/0.56    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).
% 1.43/0.56  fof(f56,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0)) | ~v2_wellord1(X0) | ~v1_relat_1(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f26])).
% 1.43/0.56  fof(f26,plain,(
% 1.43/0.56    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 1.43/0.56    inference(flattening,[],[f25])).
% 1.43/0.56  fof(f25,plain,(
% 1.43/0.56    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 1.43/0.56    inference(ennf_transformation,[],[f11])).
% 1.43/0.56  fof(f11,axiom,(
% 1.43/0.56    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).
% 1.43/0.56  fof(f59,plain,(
% 1.43/0.56    ( ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f30])).
% 1.43/0.56  % (2334)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.43/0.56  fof(f30,plain,(
% 1.43/0.56    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 1.43/0.56    inference(ennf_transformation,[],[f15])).
% 1.43/0.56  fof(f15,axiom,(
% 1.43/0.56    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).
% 1.43/0.56  fof(f60,plain,(
% 1.43/0.56    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 1.43/0.56    inference(cnf_transformation,[],[f13])).
% 1.43/0.56  fof(f13,axiom,(
% 1.43/0.56    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 1.43/0.56  fof(f228,plain,(
% 1.43/0.56    ~spl4_8 | ~spl4_2 | ~spl4_1 | ~spl4_9 | ~spl4_4),
% 1.43/0.56    inference(avatar_split_clause,[],[f218,f109,f225,f94,f99,f221])).
% 1.43/0.56  fof(f109,plain,(
% 1.43/0.56    spl4_4 <=> r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.43/0.56  fof(f218,plain,(
% 1.43/0.56    ~r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0) | ~v3_ordinal1(sK1) | ~r1_tarski(sK1,sK0) | ~spl4_4),
% 1.43/0.56    inference(resolution,[],[f203,f111])).
% 1.43/0.56  fof(f111,plain,(
% 1.43/0.56    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~spl4_4),
% 1.43/0.56    inference(avatar_component_clause,[],[f109])).
% 1.43/0.56  fof(f136,plain,(
% 1.43/0.56    spl4_6),
% 1.43/0.56    inference(avatar_contradiction_clause,[],[f133])).
% 1.43/0.56  fof(f133,plain,(
% 1.43/0.56    $false | spl4_6),
% 1.43/0.56    inference(unit_resulting_resolution,[],[f60,f123])).
% 1.43/0.56  fof(f123,plain,(
% 1.43/0.56    ~v1_relat_1(k1_wellord2(sK1)) | spl4_6),
% 1.43/0.56    inference(avatar_component_clause,[],[f121])).
% 1.43/0.56  fof(f121,plain,(
% 1.43/0.56    spl4_6 <=> v1_relat_1(k1_wellord2(sK1))),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.43/0.56  fof(f132,plain,(
% 1.43/0.56    spl4_5),
% 1.43/0.56    inference(avatar_contradiction_clause,[],[f129])).
% 1.43/0.56  fof(f129,plain,(
% 1.43/0.56    $false | spl4_5),
% 1.43/0.56    inference(unit_resulting_resolution,[],[f60,f119])).
% 1.43/0.56  fof(f119,plain,(
% 1.43/0.56    ~v1_relat_1(k1_wellord2(sK0)) | spl4_5),
% 1.43/0.56    inference(avatar_component_clause,[],[f117])).
% 1.43/0.56  fof(f117,plain,(
% 1.43/0.56    spl4_5 <=> v1_relat_1(k1_wellord2(sK0))),
% 1.43/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.43/0.56  fof(f128,plain,(
% 1.43/0.56    ~spl4_5 | ~spl4_6 | spl4_7 | ~spl4_4),
% 1.43/0.56    inference(avatar_split_clause,[],[f115,f109,f125,f121,f117])).
% 1.43/0.56  fof(f115,plain,(
% 1.43/0.56    r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | ~v1_relat_1(k1_wellord2(sK1)) | ~v1_relat_1(k1_wellord2(sK0)) | ~spl4_4),
% 1.43/0.56    inference(resolution,[],[f55,f111])).
% 1.43/0.56  fof(f55,plain,(
% 1.43/0.56    ( ! [X0,X1] : (~r4_wellord1(X0,X1) | r4_wellord1(X1,X0) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.43/0.56    inference(cnf_transformation,[],[f24])).
% 1.43/0.56  fof(f24,plain,(
% 1.43/0.56    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.43/0.56    inference(flattening,[],[f23])).
% 1.43/0.56  % (2332)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 1.43/0.56  fof(f23,plain,(
% 1.43/0.56    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.43/0.56    inference(ennf_transformation,[],[f10])).
% 1.43/0.56  fof(f10,axiom,(
% 1.43/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).
% 1.43/0.56  fof(f112,plain,(
% 1.43/0.56    spl4_4),
% 1.43/0.56    inference(avatar_split_clause,[],[f52,f109])).
% 1.43/0.56  fof(f52,plain,(
% 1.43/0.56    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 1.43/0.56    inference(cnf_transformation,[],[f40])).
% 1.43/0.56  fof(f40,plain,(
% 1.43/0.56    (sK0 != sK1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) & v3_ordinal1(sK1)) & v3_ordinal1(sK0)),
% 1.43/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f20,f39,f38])).
% 1.43/0.56  fof(f38,plain,(
% 1.43/0.56    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0)) => (? [X1] : (sK0 != X1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(sK0))),
% 1.43/0.56    introduced(choice_axiom,[])).
% 1.43/0.56  fof(f39,plain,(
% 1.43/0.56    ? [X1] : (sK0 != X1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(X1)) & v3_ordinal1(X1)) => (sK0 != sK1 & r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) & v3_ordinal1(sK1))),
% 1.43/0.56    introduced(choice_axiom,[])).
% 1.43/0.56  fof(f20,plain,(
% 1.43/0.56    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.43/0.56    inference(flattening,[],[f19])).
% 1.43/0.56  fof(f19,plain,(
% 1.43/0.56    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.43/0.56    inference(ennf_transformation,[],[f18])).
% 1.43/0.56  fof(f18,negated_conjecture,(
% 1.43/0.56    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 1.43/0.56    inference(negated_conjecture,[],[f17])).
% 1.43/0.56  fof(f17,conjecture,(
% 1.43/0.56    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 1.43/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).
% 1.43/0.56  fof(f107,plain,(
% 1.43/0.56    ~spl4_3),
% 1.43/0.56    inference(avatar_split_clause,[],[f53,f104])).
% 1.43/0.56  fof(f53,plain,(
% 1.43/0.56    sK0 != sK1),
% 1.43/0.56    inference(cnf_transformation,[],[f40])).
% 1.43/0.56  fof(f102,plain,(
% 1.43/0.56    spl4_2),
% 1.43/0.56    inference(avatar_split_clause,[],[f51,f99])).
% 1.43/0.56  fof(f51,plain,(
% 1.43/0.56    v3_ordinal1(sK1)),
% 1.43/0.56    inference(cnf_transformation,[],[f40])).
% 1.43/0.56  fof(f97,plain,(
% 1.43/0.56    spl4_1),
% 1.43/0.56    inference(avatar_split_clause,[],[f50,f94])).
% 1.43/0.56  fof(f50,plain,(
% 1.43/0.56    v3_ordinal1(sK0)),
% 1.43/0.56    inference(cnf_transformation,[],[f40])).
% 1.43/0.56  % SZS output end Proof for theBenchmark
% 1.43/0.56  % (2336)------------------------------
% 1.43/0.56  % (2336)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.56  % (2336)Termination reason: Refutation
% 1.43/0.56  
% 1.43/0.56  % (2336)Memory used [KB]: 10874
% 1.43/0.56  % (2336)Time elapsed: 0.095 s
% 1.43/0.56  % (2336)------------------------------
% 1.43/0.56  % (2336)------------------------------
% 1.43/0.57  % (2312)Success in time 0.199 s
%------------------------------------------------------------------------------
