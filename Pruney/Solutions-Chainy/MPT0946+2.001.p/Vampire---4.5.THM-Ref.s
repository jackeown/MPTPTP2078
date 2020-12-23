%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 315 expanded)
%              Number of leaves         :   34 ( 127 expanded)
%              Depth                    :   14
%              Number of atoms          :  501 ( 867 expanded)
%              Number of equality atoms :   43 (  88 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f474,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f81,f86,f91,f110,f115,f120,f129,f134,f194,f216,f228,f241,f264,f279,f295,f300,f375,f403,f431,f435,f469,f473])).

fof(f473,plain,
    ( ~ spl5_23
    | spl5_30 ),
    inference(avatar_contradiction_clause,[],[f472])).

fof(f472,plain,
    ( $false
    | ~ spl5_23
    | spl5_30 ),
    inference(subsumption_resolution,[],[f471,f43])).

fof(f43,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f471,plain,
    ( ~ v1_relat_1(k1_wellord2(sK1))
    | ~ spl5_23
    | spl5_30 ),
    inference(subsumption_resolution,[],[f470,f294])).

fof(f294,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_23 ),
    inference(avatar_component_clause,[],[f292])).

fof(f292,plain,
    ( spl5_23
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).

fof(f470,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ v1_relat_1(k1_wellord2(sK1))
    | spl5_30 ),
    inference(superposition,[],[f468,f69])).

fof(f69,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f468,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1)))
    | spl5_30 ),
    inference(avatar_component_clause,[],[f466])).

fof(f466,plain,
    ( spl5_30
  <=> r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f469,plain,
    ( ~ spl5_30
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_24
    | ~ spl5_28 ),
    inference(avatar_split_clause,[],[f463,f400,f297,f126,f117,f466])).

fof(f117,plain,
    ( spl5_6
  <=> r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f126,plain,
    ( spl5_7
  <=> v2_wellord1(k1_wellord2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f297,plain,
    ( spl5_24
  <=> k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f400,plain,
    ( spl5_28
  <=> sK0 = k1_wellord1(k1_wellord2(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).

fof(f463,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1)))
    | ~ spl5_6
    | ~ spl5_7
    | ~ spl5_24
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f462,f119])).

fof(f119,plain,
    ( r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f117])).

fof(f462,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1)))
    | ~ spl5_7
    | ~ spl5_24
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f461,f299])).

fof(f299,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f297])).

fof(f461,plain,
    ( ~ r4_wellord1(k2_wellord1(k1_wellord2(sK1),sK0),k1_wellord2(sK1))
    | ~ r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1)))
    | ~ spl5_7
    | ~ spl5_24
    | ~ spl5_28 ),
    inference(subsumption_resolution,[],[f460,f43])).

fof(f460,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | ~ r4_wellord1(k2_wellord1(k1_wellord2(sK1),sK0),k1_wellord2(sK1))
    | ~ r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1)))
    | ~ spl5_7
    | ~ spl5_24
    | ~ spl5_28 ),
    inference(forward_demodulation,[],[f458,f299])).

fof(f458,plain,
    ( ~ v1_relat_1(k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r4_wellord1(k2_wellord1(k1_wellord2(sK1),sK0),k1_wellord2(sK1))
    | ~ r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1)))
    | ~ spl5_7
    | ~ spl5_28 ),
    inference(superposition,[],[f211,f402])).

fof(f402,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl5_28 ),
    inference(avatar_component_clause,[],[f400])).

fof(f211,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0)))
        | ~ r4_wellord1(k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0)),k1_wellord2(sK1))
        | ~ r2_hidden(X0,k3_relat_1(k1_wellord2(sK1))) )
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f210,f43])).

fof(f210,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,k3_relat_1(k1_wellord2(sK1)))
        | ~ v1_relat_1(k1_wellord2(sK1))
        | ~ r4_wellord1(k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0)),k1_wellord2(sK1))
        | ~ v1_relat_1(k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0))) )
    | ~ spl5_7 ),
    inference(resolution,[],[f136,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ r4_wellord1(X0,X1)
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

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).

fof(f136,plain,
    ( ! [X0] :
        ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0)))
        | ~ r2_hidden(X0,k3_relat_1(k1_wellord2(sK1))) )
    | ~ spl5_7 ),
    inference(subsumption_resolution,[],[f135,f43])).

fof(f135,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k1_wellord2(sK1))
        | ~ r2_hidden(X0,k3_relat_1(k1_wellord2(sK1)))
        | ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0))) )
    | ~ spl5_7 ),
    inference(resolution,[],[f128,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).

fof(f128,plain,
    ( v2_wellord1(k1_wellord2(sK1))
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f126])).

fof(f435,plain,
    ( ~ spl5_21
    | spl5_29 ),
    inference(avatar_contradiction_clause,[],[f434])).

fof(f434,plain,
    ( $false
    | ~ spl5_21
    | spl5_29 ),
    inference(subsumption_resolution,[],[f433,f43])).

fof(f433,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl5_21
    | spl5_29 ),
    inference(subsumption_resolution,[],[f432,f278])).

fof(f278,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl5_21 ),
    inference(avatar_component_clause,[],[f276])).

fof(f276,plain,
    ( spl5_21
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).

fof(f432,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ v1_relat_1(k1_wellord2(sK0))
    | spl5_29 ),
    inference(superposition,[],[f430,f69])).

fof(f430,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0)))
    | spl5_29 ),
    inference(avatar_component_clause,[],[f428])).

fof(f428,plain,
    ( spl5_29
  <=> r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f431,plain,
    ( ~ spl5_29
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_19
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f426,f372,f238,f131,f117,f428])).

fof(f131,plain,
    ( spl5_8
  <=> v2_wellord1(k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f238,plain,
    ( spl5_19
  <=> k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f372,plain,
    ( spl5_27
  <=> sK1 = k1_wellord1(k1_wellord2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f426,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0)))
    | ~ spl5_6
    | ~ spl5_8
    | ~ spl5_19
    | ~ spl5_27 ),
    inference(subsumption_resolution,[],[f425,f119])).

fof(f425,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0)))
    | ~ spl5_8
    | ~ spl5_19
    | ~ spl5_27 ),
    inference(forward_demodulation,[],[f421,f240])).

fof(f240,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f238])).

fof(f421,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0)))
    | ~ spl5_8
    | ~ spl5_27 ),
    inference(superposition,[],[f138,f374])).

fof(f374,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f372])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),k1_wellord1(k1_wellord2(sK0),X0)))
        | ~ r2_hidden(X0,k3_relat_1(k1_wellord2(sK0))) )
    | ~ spl5_8 ),
    inference(subsumption_resolution,[],[f137,f43])).

fof(f137,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k1_wellord2(sK0))
        | ~ r2_hidden(X0,k3_relat_1(k1_wellord2(sK0)))
        | ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),k1_wellord1(k1_wellord2(sK0),X0))) )
    | ~ spl5_8 ),
    inference(resolution,[],[f133,f45])).

fof(f133,plain,
    ( v2_wellord1(k1_wellord2(sK0))
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f131])).

fof(f403,plain,
    ( spl5_28
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_23 ),
    inference(avatar_split_clause,[],[f396,f292,f83,f78,f400])).

fof(f78,plain,
    ( spl5_1
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f83,plain,
    ( spl5_2
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f396,plain,
    ( sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_23 ),
    inference(subsumption_resolution,[],[f393,f80])).

fof(f80,plain,
    ( v3_ordinal1(sK1)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f393,plain,
    ( ~ v3_ordinal1(sK1)
    | sK0 = k1_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl5_2
    | ~ spl5_23 ),
    inference(resolution,[],[f294,f101])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK0,X0)
        | ~ v3_ordinal1(X0)
        | sK0 = k1_wellord1(k1_wellord2(X0),sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f85,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | ~ r2_hidden(X0,X1)
      | k1_wellord1(k1_wellord2(X1),X0) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).

fof(f85,plain,
    ( v3_ordinal1(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f83])).

fof(f375,plain,
    ( spl5_27
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_21 ),
    inference(avatar_split_clause,[],[f368,f276,f83,f78,f372])).

fof(f368,plain,
    ( sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_21 ),
    inference(subsumption_resolution,[],[f365,f85])).

fof(f365,plain,
    ( ~ v3_ordinal1(sK0)
    | sK1 = k1_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl5_1
    | ~ spl5_21 ),
    inference(resolution,[],[f278,f94])).

% (23573)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% (23572)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% (23573)Refutation not found, incomplete strategy% (23573)------------------------------
% (23573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23573)Termination reason: Refutation not found, incomplete strategy

% (23573)Memory used [KB]: 6012
% (23573)Time elapsed: 0.102 s
% (23573)------------------------------
% (23573)------------------------------
% (23577)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% (23582)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% (23564)Refutation not found, incomplete strategy% (23564)------------------------------
% (23564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (23564)Termination reason: Refutation not found, incomplete strategy

% (23564)Memory used [KB]: 10618
% (23564)Time elapsed: 0.111 s
% (23564)------------------------------
% (23564)------------------------------
% (23581)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% (23578)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f94,plain,
    ( ! [X0] :
        ( ~ r2_hidden(sK1,X0)
        | ~ v3_ordinal1(X0)
        | sK1 = k1_wellord1(k1_wellord2(X0),sK1) )
    | ~ spl5_1 ),
    inference(resolution,[],[f80,f50])).

fof(f300,plain,
    ( spl5_24
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f268,f213,f297])).

fof(f213,plain,
    ( spl5_16
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f268,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl5_16 ),
    inference(resolution,[],[f215,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).

fof(f215,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f213])).

fof(f295,plain,
    ( spl5_23
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(avatar_split_clause,[],[f274,f261,f112,f78,f292])).

fof(f112,plain,
    ( spl5_5
  <=> v1_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f261,plain,
    ( spl5_20
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).

fof(f274,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl5_1
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(subsumption_resolution,[],[f272,f80])).

fof(f272,plain,
    ( ~ v3_ordinal1(sK1)
    | r2_hidden(sK0,sK1)
    | ~ spl5_5
    | ~ spl5_20 ),
    inference(resolution,[],[f263,f124])).

fof(f124,plain,
    ( ! [X1] :
        ( ~ r2_xboole_0(sK0,X1)
        | ~ v3_ordinal1(X1)
        | r2_hidden(sK0,X1) )
    | ~ spl5_5 ),
    inference(resolution,[],[f114,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | ~ r2_xboole_0(X0,X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X0,X1)
          | ~ r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v1_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_xboole_0(X0,X1)
           => r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).

fof(f114,plain,
    ( v1_ordinal1(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f112])).

fof(f263,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl5_20 ),
    inference(avatar_component_clause,[],[f261])).

fof(f279,plain,
    ( spl5_21
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_17 ),
    inference(avatar_split_clause,[],[f231,f225,f107,f83,f276])).

fof(f107,plain,
    ( spl5_4
  <=> v1_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f225,plain,
    ( spl5_17
  <=> r2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f231,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_17 ),
    inference(subsumption_resolution,[],[f229,f85])).

fof(f229,plain,
    ( ~ v3_ordinal1(sK0)
    | r2_hidden(sK1,sK0)
    | ~ spl5_4
    | ~ spl5_17 ),
    inference(resolution,[],[f227,f122])).

fof(f122,plain,
    ( ! [X1] :
        ( ~ r2_xboole_0(sK1,X1)
        | ~ v3_ordinal1(X1)
        | r2_hidden(sK1,X1) )
    | ~ spl5_4 ),
    inference(resolution,[],[f109,f44])).

fof(f109,plain,
    ( v1_ordinal1(sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f227,plain,
    ( r2_xboole_0(sK1,sK0)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f225])).

fof(f264,plain,
    ( spl5_20
    | spl5_3
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f250,f213,f88,f261])).

fof(f88,plain,
    ( spl5_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f250,plain,
    ( r2_xboole_0(sK0,sK1)
    | spl5_3
    | ~ spl5_16 ),
    inference(subsumption_resolution,[],[f247,f90])).

fof(f90,plain,
    ( sK0 != sK1
    | spl5_3 ),
    inference(avatar_component_clause,[],[f88])).

fof(f247,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK0,sK1)
    | ~ spl5_16 ),
    inference(resolution,[],[f215,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | X0 = X1
      | r2_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).

fof(f241,plain,
    ( spl5_19
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f218,f191,f238])).

fof(f191,plain,
    ( spl5_14
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f218,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl5_14 ),
    inference(resolution,[],[f193,f62])).

fof(f193,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f191])).

fof(f228,plain,
    ( spl5_17
    | spl5_3
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f220,f191,f88,f225])).

fof(f220,plain,
    ( r2_xboole_0(sK1,sK0)
    | spl5_3
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f217,f90])).

fof(f217,plain,
    ( sK0 = sK1
    | r2_xboole_0(sK1,sK0)
    | ~ spl5_14 ),
    inference(resolution,[],[f193,f68])).

fof(f216,plain,
    ( spl5_16
    | ~ spl5_1
    | ~ spl5_2
    | spl5_13 ),
    inference(avatar_split_clause,[],[f209,f187,f83,f78,f213])).

fof(f187,plain,
    ( spl5_13
  <=> r1_ordinal1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f209,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl5_1
    | ~ spl5_2
    | spl5_13 ),
    inference(subsumption_resolution,[],[f207,f80])).

fof(f207,plain,
    ( ~ v3_ordinal1(sK1)
    | r1_tarski(sK0,sK1)
    | ~ spl5_2
    | spl5_13 ),
    inference(resolution,[],[f165,f189])).

fof(f189,plain,
    ( ~ r1_ordinal1(sK1,sK0)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f187])).

fof(f165,plain,
    ( ! [X1] :
        ( r1_ordinal1(X1,sK0)
        | ~ v3_ordinal1(X1)
        | r1_tarski(sK0,X1) )
    | ~ spl5_2 ),
    inference(duplicate_literal_removal,[],[f164])).

fof(f164,plain,
    ( ! [X1] :
        ( r1_tarski(sK0,X1)
        | ~ v3_ordinal1(X1)
        | ~ v3_ordinal1(X1)
        | r1_ordinal1(X1,sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f105,f103])).

fof(f103,plain,
    ( ! [X2] :
        ( r1_ordinal1(sK0,X2)
        | ~ v3_ordinal1(X2)
        | r1_ordinal1(X2,sK0) )
    | ~ spl5_2 ),
    inference(resolution,[],[f85,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_ordinal1(X0,X1)
      | r1_ordinal1(X1,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( r1_ordinal1(X1,X0)
      | r1_ordinal1(X0,X1)
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( ( v3_ordinal1(X1)
        & v3_ordinal1(X0) )
     => ( r1_ordinal1(X1,X0)
        | r1_ordinal1(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).

fof(f105,plain,
    ( ! [X4] :
        ( ~ r1_ordinal1(sK0,X4)
        | r1_tarski(sK0,X4)
        | ~ v3_ordinal1(X4) )
    | ~ spl5_2 ),
    inference(resolution,[],[f85,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r1_tarski(X0,X1)
      | ~ r1_ordinal1(X0,X1) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( r1_ordinal1(X0,X1)
      <=> r1_tarski(X0,X1) )
      | ~ v3_ordinal1(X1)
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f194,plain,
    ( ~ spl5_13
    | spl5_14
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f149,f83,f78,f191,f187])).

fof(f149,plain,
    ( r1_tarski(sK1,sK0)
    | ~ r1_ordinal1(sK1,sK0)
    | ~ spl5_1
    | ~ spl5_2 ),
    inference(resolution,[],[f98,f85])).

fof(f98,plain,
    ( ! [X4] :
        ( ~ v3_ordinal1(X4)
        | r1_tarski(sK1,X4)
        | ~ r1_ordinal1(sK1,X4) )
    | ~ spl5_1 ),
    inference(resolution,[],[f80,f65])).

fof(f134,plain,
    ( spl5_8
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f99,f83,f131])).

fof(f99,plain,
    ( v2_wellord1(k1_wellord2(sK0))
    | ~ spl5_2 ),
    inference(resolution,[],[f85,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v2_wellord1(k1_wellord2(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).

fof(f129,plain,
    ( spl5_7
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f92,f78,f126])).

fof(f92,plain,
    ( v2_wellord1(k1_wellord2(sK1))
    | ~ spl5_1 ),
    inference(resolution,[],[f80,f47])).

fof(f120,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f40,f117])).

fof(f40,plain,(
    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).

fof(f115,plain,
    ( spl5_5
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f100,f83,f112])).

fof(f100,plain,
    ( v1_ordinal1(sK0)
    | ~ spl5_2 ),
    inference(resolution,[],[f85,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v1_ordinal1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_ordinal1(X0)
        & v1_ordinal1(X0) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ( v2_ordinal1(X0)
        & v1_ordinal1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).

fof(f110,plain,
    ( spl5_4
    | ~ spl5_1 ),
    inference(avatar_split_clause,[],[f93,f78,f107])).

fof(f93,plain,
    ( v1_ordinal1(sK1)
    | ~ spl5_1 ),
    inference(resolution,[],[f80,f48])).

fof(f91,plain,(
    ~ spl5_3 ),
    inference(avatar_split_clause,[],[f41,f88])).

fof(f41,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f18])).

fof(f86,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f42,f83])).

fof(f42,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f81,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f39,f78])).

fof(f39,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f18])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:01:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (23575)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (23563)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (23563)Refutation not found, incomplete strategy% (23563)------------------------------
% 0.21/0.48  % (23563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (23571)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (23563)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (23563)Memory used [KB]: 6140
% 0.21/0.48  % (23563)Time elapsed: 0.070 s
% 0.21/0.48  % (23563)------------------------------
% 0.21/0.48  % (23563)------------------------------
% 0.21/0.49  % (23583)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.49  % (23583)Refutation not found, incomplete strategy% (23583)------------------------------
% 0.21/0.49  % (23583)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (23583)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (23583)Memory used [KB]: 10618
% 0.21/0.49  % (23583)Time elapsed: 0.081 s
% 0.21/0.49  % (23583)------------------------------
% 0.21/0.49  % (23583)------------------------------
% 0.21/0.49  % (23569)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (23565)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (23576)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.50  % (23576)Refutation not found, incomplete strategy% (23576)------------------------------
% 0.21/0.50  % (23576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (23576)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (23576)Memory used [KB]: 1663
% 0.21/0.50  % (23576)Time elapsed: 0.044 s
% 0.21/0.50  % (23576)------------------------------
% 0.21/0.50  % (23576)------------------------------
% 0.21/0.50  % (23579)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.50  % (23574)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.50  % (23564)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (23574)Refutation not found, incomplete strategy% (23574)------------------------------
% 0.21/0.50  % (23574)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (23574)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (23574)Memory used [KB]: 10618
% 0.21/0.50  % (23574)Time elapsed: 0.096 s
% 0.21/0.50  % (23574)------------------------------
% 0.21/0.50  % (23574)------------------------------
% 0.21/0.51  % (23567)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (23570)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.51  % (23568)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (23566)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (23580)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (23566)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f474,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f81,f86,f91,f110,f115,f120,f129,f134,f194,f216,f228,f241,f264,f279,f295,f300,f375,f403,f431,f435,f469,f473])).
% 0.21/0.51  fof(f473,plain,(
% 0.21/0.51    ~spl5_23 | spl5_30),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f472])).
% 0.21/0.51  fof(f472,plain,(
% 0.21/0.51    $false | (~spl5_23 | spl5_30)),
% 0.21/0.51    inference(subsumption_resolution,[],[f471,f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.21/0.51  fof(f471,plain,(
% 0.21/0.51    ~v1_relat_1(k1_wellord2(sK1)) | (~spl5_23 | spl5_30)),
% 0.21/0.51    inference(subsumption_resolution,[],[f470,f294])).
% 0.21/0.51  fof(f294,plain,(
% 0.21/0.51    r2_hidden(sK0,sK1) | ~spl5_23),
% 0.21/0.51    inference(avatar_component_clause,[],[f292])).
% 0.21/0.51  fof(f292,plain,(
% 0.21/0.51    spl5_23 <=> r2_hidden(sK0,sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_23])])).
% 0.21/0.51  fof(f470,plain,(
% 0.21/0.51    ~r2_hidden(sK0,sK1) | ~v1_relat_1(k1_wellord2(sK1)) | spl5_30),
% 0.21/0.51    inference(superposition,[],[f468,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.21/0.51    inference(equality_resolution,[],[f60])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_wellord2)).
% 0.21/0.51  fof(f468,plain,(
% 0.21/0.51    ~r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1))) | spl5_30),
% 0.21/0.51    inference(avatar_component_clause,[],[f466])).
% 0.21/0.51  fof(f466,plain,(
% 0.21/0.51    spl5_30 <=> r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.21/0.51  fof(f469,plain,(
% 0.21/0.51    ~spl5_30 | ~spl5_6 | ~spl5_7 | ~spl5_24 | ~spl5_28),
% 0.21/0.51    inference(avatar_split_clause,[],[f463,f400,f297,f126,f117,f466])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    spl5_6 <=> r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    spl5_7 <=> v2_wellord1(k1_wellord2(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.51  fof(f297,plain,(
% 0.21/0.51    spl5_24 <=> k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 0.21/0.51  fof(f400,plain,(
% 0.21/0.51    spl5_28 <=> sK0 = k1_wellord1(k1_wellord2(sK1),sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_28])])).
% 0.21/0.51  fof(f463,plain,(
% 0.21/0.51    ~r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1))) | (~spl5_6 | ~spl5_7 | ~spl5_24 | ~spl5_28)),
% 0.21/0.51    inference(subsumption_resolution,[],[f462,f119])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~spl5_6),
% 0.21/0.51    inference(avatar_component_clause,[],[f117])).
% 0.21/0.51  fof(f462,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1))) | (~spl5_7 | ~spl5_24 | ~spl5_28)),
% 0.21/0.51    inference(forward_demodulation,[],[f461,f299])).
% 0.21/0.51  fof(f299,plain,(
% 0.21/0.51    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) | ~spl5_24),
% 0.21/0.51    inference(avatar_component_clause,[],[f297])).
% 0.21/0.51  fof(f461,plain,(
% 0.21/0.51    ~r4_wellord1(k2_wellord1(k1_wellord2(sK1),sK0),k1_wellord2(sK1)) | ~r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1))) | (~spl5_7 | ~spl5_24 | ~spl5_28)),
% 0.21/0.51    inference(subsumption_resolution,[],[f460,f43])).
% 0.21/0.51  fof(f460,plain,(
% 0.21/0.51    ~v1_relat_1(k1_wellord2(sK0)) | ~r4_wellord1(k2_wellord1(k1_wellord2(sK1),sK0),k1_wellord2(sK1)) | ~r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1))) | (~spl5_7 | ~spl5_24 | ~spl5_28)),
% 0.21/0.51    inference(forward_demodulation,[],[f458,f299])).
% 0.21/0.51  fof(f458,plain,(
% 0.21/0.51    ~v1_relat_1(k2_wellord1(k1_wellord2(sK1),sK0)) | ~r4_wellord1(k2_wellord1(k1_wellord2(sK1),sK0),k1_wellord2(sK1)) | ~r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1))) | (~spl5_7 | ~spl5_28)),
% 0.21/0.51    inference(superposition,[],[f211,f402])).
% 0.21/0.51  fof(f402,plain,(
% 0.21/0.51    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | ~spl5_28),
% 0.21/0.51    inference(avatar_component_clause,[],[f400])).
% 0.21/0.51  fof(f211,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0))) | ~r4_wellord1(k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0)),k1_wellord2(sK1)) | ~r2_hidden(X0,k3_relat_1(k1_wellord2(sK1)))) ) | ~spl5_7),
% 0.21/0.51    inference(subsumption_resolution,[],[f210,f43])).
% 0.21/0.51  fof(f210,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(X0,k3_relat_1(k1_wellord2(sK1))) | ~v1_relat_1(k1_wellord2(sK1)) | ~r4_wellord1(k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0)),k1_wellord2(sK1)) | ~v1_relat_1(k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0)))) ) | ~spl5_7),
% 0.21/0.51    inference(resolution,[],[f136,f46])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    ( ! [X0,X1] : (r4_wellord1(X1,X0) | ~v1_relat_1(X1) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_wellord1)).
% 0.21/0.51  fof(f136,plain,(
% 0.21/0.51    ( ! [X0] : (~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0))) | ~r2_hidden(X0,k3_relat_1(k1_wellord2(sK1)))) ) | ~spl5_7),
% 0.21/0.51    inference(subsumption_resolution,[],[f135,f43])).
% 0.21/0.51  fof(f135,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(k1_wellord2(sK1)) | ~r2_hidden(X0,k3_relat_1(k1_wellord2(sK1))) | ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0)))) ) | ~spl5_7),
% 0.21/0.51    inference(resolution,[],[f128,f45])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_wellord1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k3_relat_1(X0)) | ~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f21])).
% 0.21/0.51  fof(f21,plain,(
% 0.21/0.51    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_wellord1)).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    v2_wellord1(k1_wellord2(sK1)) | ~spl5_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f126])).
% 0.21/0.51  fof(f435,plain,(
% 0.21/0.51    ~spl5_21 | spl5_29),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f434])).
% 0.21/0.51  fof(f434,plain,(
% 0.21/0.51    $false | (~spl5_21 | spl5_29)),
% 0.21/0.51    inference(subsumption_resolution,[],[f433,f43])).
% 0.21/0.51  fof(f433,plain,(
% 0.21/0.51    ~v1_relat_1(k1_wellord2(sK0)) | (~spl5_21 | spl5_29)),
% 0.21/0.51    inference(subsumption_resolution,[],[f432,f278])).
% 0.21/0.51  fof(f278,plain,(
% 0.21/0.51    r2_hidden(sK1,sK0) | ~spl5_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f276])).
% 0.21/0.51  fof(f276,plain,(
% 0.21/0.51    spl5_21 <=> r2_hidden(sK1,sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_21])])).
% 0.21/0.51  fof(f432,plain,(
% 0.21/0.51    ~r2_hidden(sK1,sK0) | ~v1_relat_1(k1_wellord2(sK0)) | spl5_29),
% 0.21/0.51    inference(superposition,[],[f430,f69])).
% 0.21/0.51  fof(f430,plain,(
% 0.21/0.51    ~r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0))) | spl5_29),
% 0.21/0.51    inference(avatar_component_clause,[],[f428])).
% 0.21/0.51  fof(f428,plain,(
% 0.21/0.51    spl5_29 <=> r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0)))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.21/0.51  fof(f431,plain,(
% 0.21/0.51    ~spl5_29 | ~spl5_6 | ~spl5_8 | ~spl5_19 | ~spl5_27),
% 0.21/0.51    inference(avatar_split_clause,[],[f426,f372,f238,f131,f117,f428])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    spl5_8 <=> v2_wellord1(k1_wellord2(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.51  fof(f238,plain,(
% 0.21/0.51    spl5_19 <=> k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.51  fof(f372,plain,(
% 0.21/0.51    spl5_27 <=> sK1 = k1_wellord1(k1_wellord2(sK0),sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 0.21/0.51  fof(f426,plain,(
% 0.21/0.51    ~r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0))) | (~spl5_6 | ~spl5_8 | ~spl5_19 | ~spl5_27)),
% 0.21/0.51    inference(subsumption_resolution,[],[f425,f119])).
% 0.21/0.51  fof(f425,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0))) | (~spl5_8 | ~spl5_19 | ~spl5_27)),
% 0.21/0.51    inference(forward_demodulation,[],[f421,f240])).
% 0.21/0.51  fof(f240,plain,(
% 0.21/0.51    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | ~spl5_19),
% 0.21/0.51    inference(avatar_component_clause,[],[f238])).
% 0.21/0.51  fof(f421,plain,(
% 0.21/0.51    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0))) | (~spl5_8 | ~spl5_27)),
% 0.21/0.51    inference(superposition,[],[f138,f374])).
% 0.21/0.51  fof(f374,plain,(
% 0.21/0.51    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | ~spl5_27),
% 0.21/0.51    inference(avatar_component_clause,[],[f372])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    ( ! [X0] : (~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),k1_wellord1(k1_wellord2(sK0),X0))) | ~r2_hidden(X0,k3_relat_1(k1_wellord2(sK0)))) ) | ~spl5_8),
% 0.21/0.51    inference(subsumption_resolution,[],[f137,f43])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_relat_1(k1_wellord2(sK0)) | ~r2_hidden(X0,k3_relat_1(k1_wellord2(sK0))) | ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),k1_wellord1(k1_wellord2(sK0),X0)))) ) | ~spl5_8),
% 0.21/0.51    inference(resolution,[],[f133,f45])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    v2_wellord1(k1_wellord2(sK0)) | ~spl5_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f131])).
% 0.21/0.51  fof(f403,plain,(
% 0.21/0.51    spl5_28 | ~spl5_1 | ~spl5_2 | ~spl5_23),
% 0.21/0.51    inference(avatar_split_clause,[],[f396,f292,f83,f78,f400])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    spl5_1 <=> v3_ordinal1(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    spl5_2 <=> v3_ordinal1(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.51  fof(f396,plain,(
% 0.21/0.51    sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | (~spl5_1 | ~spl5_2 | ~spl5_23)),
% 0.21/0.51    inference(subsumption_resolution,[],[f393,f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    v3_ordinal1(sK1) | ~spl5_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f78])).
% 0.21/0.51  fof(f393,plain,(
% 0.21/0.51    ~v3_ordinal1(sK1) | sK0 = k1_wellord1(k1_wellord2(sK1),sK0) | (~spl5_2 | ~spl5_23)),
% 0.21/0.51    inference(resolution,[],[f294,f101])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    ( ! [X0] : (~r2_hidden(sK0,X0) | ~v3_ordinal1(X0) | sK0 = k1_wellord1(k1_wellord2(X0),sK0)) ) | ~spl5_2),
% 0.21/0.51    inference(resolution,[],[f85,f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | ~r2_hidden(X0,X1) | k1_wellord1(k1_wellord2(X1),X0) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(flattening,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_wellord2)).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    v3_ordinal1(sK0) | ~spl5_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f83])).
% 0.21/0.51  fof(f375,plain,(
% 0.21/0.51    spl5_27 | ~spl5_1 | ~spl5_2 | ~spl5_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f368,f276,f83,f78,f372])).
% 0.21/0.51  fof(f368,plain,(
% 0.21/0.51    sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | (~spl5_1 | ~spl5_2 | ~spl5_21)),
% 0.21/0.51    inference(subsumption_resolution,[],[f365,f85])).
% 0.21/0.51  fof(f365,plain,(
% 0.21/0.51    ~v3_ordinal1(sK0) | sK1 = k1_wellord1(k1_wellord2(sK0),sK1) | (~spl5_1 | ~spl5_21)),
% 0.21/0.51    inference(resolution,[],[f278,f94])).
% 0.21/0.51  % (23573)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (23572)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.52  % (23573)Refutation not found, incomplete strategy% (23573)------------------------------
% 0.21/0.52  % (23573)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23573)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (23573)Memory used [KB]: 6012
% 0.21/0.52  % (23573)Time elapsed: 0.102 s
% 0.21/0.52  % (23573)------------------------------
% 0.21/0.52  % (23573)------------------------------
% 0.21/0.52  % (23577)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.52  % (23582)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.52  % (23564)Refutation not found, incomplete strategy% (23564)------------------------------
% 0.21/0.52  % (23564)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (23564)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (23564)Memory used [KB]: 10618
% 0.21/0.52  % (23564)Time elapsed: 0.111 s
% 0.21/0.52  % (23564)------------------------------
% 0.21/0.52  % (23564)------------------------------
% 0.21/0.52  % (23581)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 1.33/0.53  % (23578)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 1.33/0.53  fof(f94,plain,(
% 1.33/0.53    ( ! [X0] : (~r2_hidden(sK1,X0) | ~v3_ordinal1(X0) | sK1 = k1_wellord1(k1_wellord2(X0),sK1)) ) | ~spl5_1),
% 1.33/0.53    inference(resolution,[],[f80,f50])).
% 1.33/0.53  fof(f300,plain,(
% 1.33/0.53    spl5_24 | ~spl5_16),
% 1.33/0.53    inference(avatar_split_clause,[],[f268,f213,f297])).
% 1.33/0.53  fof(f213,plain,(
% 1.33/0.53    spl5_16 <=> r1_tarski(sK0,sK1)),
% 1.33/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.33/0.53  fof(f268,plain,(
% 1.33/0.53    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) | ~spl5_16),
% 1.33/0.53    inference(resolution,[],[f215,f62])).
% 1.33/0.53  fof(f62,plain,(
% 1.33/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f34])).
% 1.33/0.53  fof(f34,plain,(
% 1.33/0.53    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 1.33/0.53    inference(ennf_transformation,[],[f14])).
% 1.33/0.53  fof(f14,axiom,(
% 1.33/0.53    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_wellord2)).
% 1.33/0.53  fof(f215,plain,(
% 1.33/0.53    r1_tarski(sK0,sK1) | ~spl5_16),
% 1.33/0.53    inference(avatar_component_clause,[],[f213])).
% 1.33/0.53  fof(f295,plain,(
% 1.33/0.53    spl5_23 | ~spl5_1 | ~spl5_5 | ~spl5_20),
% 1.33/0.53    inference(avatar_split_clause,[],[f274,f261,f112,f78,f292])).
% 1.33/0.53  fof(f112,plain,(
% 1.33/0.53    spl5_5 <=> v1_ordinal1(sK0)),
% 1.33/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.33/0.53  fof(f261,plain,(
% 1.33/0.53    spl5_20 <=> r2_xboole_0(sK0,sK1)),
% 1.33/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_20])])).
% 1.33/0.53  fof(f274,plain,(
% 1.33/0.53    r2_hidden(sK0,sK1) | (~spl5_1 | ~spl5_5 | ~spl5_20)),
% 1.33/0.53    inference(subsumption_resolution,[],[f272,f80])).
% 1.33/0.53  fof(f272,plain,(
% 1.33/0.53    ~v3_ordinal1(sK1) | r2_hidden(sK0,sK1) | (~spl5_5 | ~spl5_20)),
% 1.33/0.53    inference(resolution,[],[f263,f124])).
% 1.33/0.53  fof(f124,plain,(
% 1.33/0.53    ( ! [X1] : (~r2_xboole_0(sK0,X1) | ~v3_ordinal1(X1) | r2_hidden(sK0,X1)) ) | ~spl5_5),
% 1.33/0.53    inference(resolution,[],[f114,f44])).
% 1.33/0.53  fof(f44,plain,(
% 1.33/0.53    ( ! [X0,X1] : (~v1_ordinal1(X0) | ~v3_ordinal1(X1) | ~r2_xboole_0(X0,X1) | r2_hidden(X0,X1)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f20])).
% 1.33/0.53  fof(f20,plain,(
% 1.33/0.53    ! [X0] : (! [X1] : (r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 1.33/0.53    inference(flattening,[],[f19])).
% 1.33/0.53  fof(f19,plain,(
% 1.33/0.53    ! [X0] : (! [X1] : ((r2_hidden(X0,X1) | ~r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v1_ordinal1(X0))),
% 1.33/0.53    inference(ennf_transformation,[],[f6])).
% 1.33/0.53  fof(f6,axiom,(
% 1.33/0.53    ! [X0] : (v1_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_xboole_0(X0,X1) => r2_hidden(X0,X1))))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_ordinal1)).
% 1.33/0.53  fof(f114,plain,(
% 1.33/0.53    v1_ordinal1(sK0) | ~spl5_5),
% 1.33/0.53    inference(avatar_component_clause,[],[f112])).
% 1.33/0.53  fof(f263,plain,(
% 1.33/0.53    r2_xboole_0(sK0,sK1) | ~spl5_20),
% 1.33/0.53    inference(avatar_component_clause,[],[f261])).
% 1.33/0.53  fof(f279,plain,(
% 1.33/0.53    spl5_21 | ~spl5_2 | ~spl5_4 | ~spl5_17),
% 1.33/0.53    inference(avatar_split_clause,[],[f231,f225,f107,f83,f276])).
% 1.33/0.53  fof(f107,plain,(
% 1.33/0.53    spl5_4 <=> v1_ordinal1(sK1)),
% 1.33/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.33/0.53  fof(f225,plain,(
% 1.33/0.53    spl5_17 <=> r2_xboole_0(sK1,sK0)),
% 1.33/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.33/0.53  fof(f231,plain,(
% 1.33/0.53    r2_hidden(sK1,sK0) | (~spl5_2 | ~spl5_4 | ~spl5_17)),
% 1.33/0.53    inference(subsumption_resolution,[],[f229,f85])).
% 1.33/0.53  fof(f229,plain,(
% 1.33/0.53    ~v3_ordinal1(sK0) | r2_hidden(sK1,sK0) | (~spl5_4 | ~spl5_17)),
% 1.33/0.53    inference(resolution,[],[f227,f122])).
% 1.33/0.53  fof(f122,plain,(
% 1.33/0.53    ( ! [X1] : (~r2_xboole_0(sK1,X1) | ~v3_ordinal1(X1) | r2_hidden(sK1,X1)) ) | ~spl5_4),
% 1.33/0.53    inference(resolution,[],[f109,f44])).
% 1.33/0.53  fof(f109,plain,(
% 1.33/0.53    v1_ordinal1(sK1) | ~spl5_4),
% 1.33/0.53    inference(avatar_component_clause,[],[f107])).
% 1.33/0.53  fof(f227,plain,(
% 1.33/0.53    r2_xboole_0(sK1,sK0) | ~spl5_17),
% 1.33/0.53    inference(avatar_component_clause,[],[f225])).
% 1.33/0.53  fof(f264,plain,(
% 1.33/0.53    spl5_20 | spl5_3 | ~spl5_16),
% 1.33/0.53    inference(avatar_split_clause,[],[f250,f213,f88,f261])).
% 1.33/0.53  fof(f88,plain,(
% 1.33/0.53    spl5_3 <=> sK0 = sK1),
% 1.33/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.33/0.53  fof(f250,plain,(
% 1.33/0.53    r2_xboole_0(sK0,sK1) | (spl5_3 | ~spl5_16)),
% 1.33/0.53    inference(subsumption_resolution,[],[f247,f90])).
% 1.33/0.53  fof(f90,plain,(
% 1.33/0.53    sK0 != sK1 | spl5_3),
% 1.33/0.53    inference(avatar_component_clause,[],[f88])).
% 1.33/0.53  fof(f247,plain,(
% 1.33/0.53    sK0 = sK1 | r2_xboole_0(sK0,sK1) | ~spl5_16),
% 1.33/0.53    inference(resolution,[],[f215,f68])).
% 1.33/0.53  fof(f68,plain,(
% 1.33/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | X0 = X1 | r2_xboole_0(X0,X1)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f1])).
% 1.33/0.53  fof(f1,axiom,(
% 1.33/0.53    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d8_xboole_0)).
% 1.33/0.53  fof(f241,plain,(
% 1.33/0.53    spl5_19 | ~spl5_14),
% 1.33/0.53    inference(avatar_split_clause,[],[f218,f191,f238])).
% 1.33/0.53  fof(f191,plain,(
% 1.33/0.53    spl5_14 <=> r1_tarski(sK1,sK0)),
% 1.33/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.33/0.53  fof(f218,plain,(
% 1.33/0.53    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | ~spl5_14),
% 1.33/0.53    inference(resolution,[],[f193,f62])).
% 1.33/0.53  fof(f193,plain,(
% 1.33/0.53    r1_tarski(sK1,sK0) | ~spl5_14),
% 1.33/0.53    inference(avatar_component_clause,[],[f191])).
% 1.33/0.53  fof(f228,plain,(
% 1.33/0.53    spl5_17 | spl5_3 | ~spl5_14),
% 1.33/0.53    inference(avatar_split_clause,[],[f220,f191,f88,f225])).
% 1.33/0.53  fof(f220,plain,(
% 1.33/0.53    r2_xboole_0(sK1,sK0) | (spl5_3 | ~spl5_14)),
% 1.33/0.53    inference(subsumption_resolution,[],[f217,f90])).
% 1.33/0.53  fof(f217,plain,(
% 1.33/0.53    sK0 = sK1 | r2_xboole_0(sK1,sK0) | ~spl5_14),
% 1.33/0.53    inference(resolution,[],[f193,f68])).
% 1.33/0.53  fof(f216,plain,(
% 1.33/0.53    spl5_16 | ~spl5_1 | ~spl5_2 | spl5_13),
% 1.33/0.53    inference(avatar_split_clause,[],[f209,f187,f83,f78,f213])).
% 1.33/0.53  fof(f187,plain,(
% 1.33/0.53    spl5_13 <=> r1_ordinal1(sK1,sK0)),
% 1.33/0.53    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.33/0.53  fof(f209,plain,(
% 1.33/0.53    r1_tarski(sK0,sK1) | (~spl5_1 | ~spl5_2 | spl5_13)),
% 1.33/0.53    inference(subsumption_resolution,[],[f207,f80])).
% 1.33/0.53  fof(f207,plain,(
% 1.33/0.53    ~v3_ordinal1(sK1) | r1_tarski(sK0,sK1) | (~spl5_2 | spl5_13)),
% 1.33/0.53    inference(resolution,[],[f165,f189])).
% 1.33/0.53  fof(f189,plain,(
% 1.33/0.53    ~r1_ordinal1(sK1,sK0) | spl5_13),
% 1.33/0.53    inference(avatar_component_clause,[],[f187])).
% 1.33/0.53  fof(f165,plain,(
% 1.33/0.53    ( ! [X1] : (r1_ordinal1(X1,sK0) | ~v3_ordinal1(X1) | r1_tarski(sK0,X1)) ) | ~spl5_2),
% 1.33/0.53    inference(duplicate_literal_removal,[],[f164])).
% 1.33/0.53  fof(f164,plain,(
% 1.33/0.53    ( ! [X1] : (r1_tarski(sK0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X1) | r1_ordinal1(X1,sK0)) ) | ~spl5_2),
% 1.33/0.53    inference(resolution,[],[f105,f103])).
% 1.33/0.53  fof(f103,plain,(
% 1.33/0.53    ( ! [X2] : (r1_ordinal1(sK0,X2) | ~v3_ordinal1(X2) | r1_ordinal1(X2,sK0)) ) | ~spl5_2),
% 1.33/0.53    inference(resolution,[],[f85,f63])).
% 1.33/0.53  fof(f63,plain,(
% 1.33/0.53    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_ordinal1(X0,X1) | r1_ordinal1(X1,X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f36])).
% 1.33/0.53  fof(f36,plain,(
% 1.33/0.53    ! [X0,X1] : (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.33/0.53    inference(flattening,[],[f35])).
% 1.33/0.53  fof(f35,plain,(
% 1.33/0.53    ! [X0,X1] : ((r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.33/0.53    inference(ennf_transformation,[],[f3])).
% 1.33/0.53  fof(f3,axiom,(
% 1.33/0.53    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X1,X0) | r1_ordinal1(X0,X1)))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',connectedness_r1_ordinal1)).
% 1.33/0.53  fof(f105,plain,(
% 1.33/0.53    ( ! [X4] : (~r1_ordinal1(sK0,X4) | r1_tarski(sK0,X4) | ~v3_ordinal1(X4)) ) | ~spl5_2),
% 1.33/0.53    inference(resolution,[],[f85,f65])).
% 1.33/0.53  fof(f65,plain,(
% 1.33/0.53    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r1_tarski(X0,X1) | ~r1_ordinal1(X0,X1)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f38])).
% 1.33/0.53  fof(f38,plain,(
% 1.33/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | ~v3_ordinal1(X1) | ~v3_ordinal1(X0))),
% 1.33/0.53    inference(flattening,[],[f37])).
% 1.33/0.53  fof(f37,plain,(
% 1.33/0.53    ! [X0,X1] : ((r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)) | (~v3_ordinal1(X1) | ~v3_ordinal1(X0)))),
% 1.33/0.53    inference(ennf_transformation,[],[f5])).
% 1.33/0.53  fof(f5,axiom,(
% 1.33/0.53    ! [X0,X1] : ((v3_ordinal1(X1) & v3_ordinal1(X0)) => (r1_ordinal1(X0,X1) <=> r1_tarski(X0,X1)))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r1_ordinal1)).
% 1.33/0.53  fof(f194,plain,(
% 1.33/0.53    ~spl5_13 | spl5_14 | ~spl5_1 | ~spl5_2),
% 1.33/0.53    inference(avatar_split_clause,[],[f149,f83,f78,f191,f187])).
% 1.33/0.53  fof(f149,plain,(
% 1.33/0.53    r1_tarski(sK1,sK0) | ~r1_ordinal1(sK1,sK0) | (~spl5_1 | ~spl5_2)),
% 1.33/0.53    inference(resolution,[],[f98,f85])).
% 1.33/0.53  fof(f98,plain,(
% 1.33/0.53    ( ! [X4] : (~v3_ordinal1(X4) | r1_tarski(sK1,X4) | ~r1_ordinal1(sK1,X4)) ) | ~spl5_1),
% 1.33/0.53    inference(resolution,[],[f80,f65])).
% 1.33/0.53  fof(f134,plain,(
% 1.33/0.53    spl5_8 | ~spl5_2),
% 1.33/0.53    inference(avatar_split_clause,[],[f99,f83,f131])).
% 1.33/0.53  fof(f99,plain,(
% 1.33/0.53    v2_wellord1(k1_wellord2(sK0)) | ~spl5_2),
% 1.33/0.53    inference(resolution,[],[f85,f47])).
% 1.33/0.53  fof(f47,plain,(
% 1.33/0.53    ( ! [X0] : (~v3_ordinal1(X0) | v2_wellord1(k1_wellord2(X0))) )),
% 1.33/0.53    inference(cnf_transformation,[],[f25])).
% 1.33/0.53  fof(f25,plain,(
% 1.33/0.53    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 1.33/0.53    inference(ennf_transformation,[],[f13])).
% 1.33/0.53  fof(f13,axiom,(
% 1.33/0.53    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_wellord2)).
% 1.33/0.53  fof(f129,plain,(
% 1.33/0.53    spl5_7 | ~spl5_1),
% 1.33/0.53    inference(avatar_split_clause,[],[f92,f78,f126])).
% 1.33/0.53  fof(f92,plain,(
% 1.33/0.53    v2_wellord1(k1_wellord2(sK1)) | ~spl5_1),
% 1.33/0.53    inference(resolution,[],[f80,f47])).
% 1.33/0.53  fof(f120,plain,(
% 1.33/0.53    spl5_6),
% 1.33/0.53    inference(avatar_split_clause,[],[f40,f117])).
% 1.33/0.53  fof(f40,plain,(
% 1.33/0.53    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 1.33/0.53    inference(cnf_transformation,[],[f18])).
% 1.33/0.53  fof(f18,plain,(
% 1.33/0.53    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.33/0.53    inference(flattening,[],[f17])).
% 1.33/0.53  fof(f17,plain,(
% 1.33/0.53    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 1.33/0.53    inference(ennf_transformation,[],[f16])).
% 1.33/0.53  fof(f16,negated_conjecture,(
% 1.33/0.53    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 1.33/0.53    inference(negated_conjecture,[],[f15])).
% 1.33/0.53  fof(f15,conjecture,(
% 1.33/0.53    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_wellord2)).
% 1.33/0.53  fof(f115,plain,(
% 1.33/0.53    spl5_5 | ~spl5_2),
% 1.33/0.53    inference(avatar_split_clause,[],[f100,f83,f112])).
% 1.33/0.53  fof(f100,plain,(
% 1.33/0.53    v1_ordinal1(sK0) | ~spl5_2),
% 1.33/0.53    inference(resolution,[],[f85,f48])).
% 1.33/0.53  fof(f48,plain,(
% 1.33/0.53    ( ! [X0] : (~v3_ordinal1(X0) | v1_ordinal1(X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f26])).
% 1.33/0.53  fof(f26,plain,(
% 1.33/0.53    ! [X0] : ((v2_ordinal1(X0) & v1_ordinal1(X0)) | ~v3_ordinal1(X0))),
% 1.33/0.53    inference(ennf_transformation,[],[f2])).
% 1.33/0.53  fof(f2,axiom,(
% 1.33/0.53    ! [X0] : (v3_ordinal1(X0) => (v2_ordinal1(X0) & v1_ordinal1(X0)))),
% 1.33/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_ordinal1)).
% 1.33/0.53  fof(f110,plain,(
% 1.33/0.53    spl5_4 | ~spl5_1),
% 1.33/0.53    inference(avatar_split_clause,[],[f93,f78,f107])).
% 1.33/0.53  fof(f93,plain,(
% 1.33/0.53    v1_ordinal1(sK1) | ~spl5_1),
% 1.33/0.53    inference(resolution,[],[f80,f48])).
% 1.33/0.53  fof(f91,plain,(
% 1.33/0.53    ~spl5_3),
% 1.33/0.53    inference(avatar_split_clause,[],[f41,f88])).
% 1.33/0.53  fof(f41,plain,(
% 1.33/0.53    sK0 != sK1),
% 1.33/0.53    inference(cnf_transformation,[],[f18])).
% 1.33/0.53  fof(f86,plain,(
% 1.33/0.53    spl5_2),
% 1.33/0.53    inference(avatar_split_clause,[],[f42,f83])).
% 1.33/0.53  fof(f42,plain,(
% 1.33/0.53    v3_ordinal1(sK0)),
% 1.33/0.53    inference(cnf_transformation,[],[f18])).
% 1.33/0.53  fof(f81,plain,(
% 1.33/0.53    spl5_1),
% 1.33/0.53    inference(avatar_split_clause,[],[f39,f78])).
% 1.33/0.53  fof(f39,plain,(
% 1.33/0.53    v3_ordinal1(sK1)),
% 1.33/0.53    inference(cnf_transformation,[],[f18])).
% 1.33/0.53  % SZS output end Proof for theBenchmark
% 1.33/0.53  % (23566)------------------------------
% 1.33/0.53  % (23566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (23566)Termination reason: Refutation
% 1.33/0.53  
% 1.33/0.53  % (23566)Memory used [KB]: 10746
% 1.33/0.53  % (23566)Time elapsed: 0.111 s
% 1.33/0.53  % (23566)------------------------------
% 1.33/0.53  % (23566)------------------------------
% 1.33/0.53  % (23562)Success in time 0.166 s
%------------------------------------------------------------------------------
