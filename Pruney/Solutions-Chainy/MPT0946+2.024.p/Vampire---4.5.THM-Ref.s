%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:00:03 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 264 expanded)
%              Number of leaves         :   30 ( 107 expanded)
%              Depth                    :   12
%              Number of atoms          :  439 ( 728 expanded)
%              Number of equality atoms :   45 (  83 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f298,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f66,f71,f76,f89,f94,f99,f117,f129,f145,f177,f200,f208,f221,f233,f245,f255,f261,f274,f282,f297])).

fof(f297,plain,
    ( ~ spl4_4
    | spl4_25 ),
    inference(avatar_contradiction_clause,[],[f296])).

fof(f296,plain,
    ( $false
    | ~ spl4_4
    | spl4_25 ),
    inference(subsumption_resolution,[],[f295,f35])).

fof(f35,plain,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : v1_relat_1(k1_wellord2(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).

fof(f295,plain,
    ( ~ v1_relat_1(k1_wellord2(sK0))
    | ~ spl4_4
    | spl4_25 ),
    inference(subsumption_resolution,[],[f294,f88])).

fof(f88,plain,
    ( r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl4_4
  <=> r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f294,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ v1_relat_1(k1_wellord2(sK0))
    | spl4_25 ),
    inference(subsumption_resolution,[],[f293,f35])).

fof(f293,plain,
    ( ~ v1_relat_1(k1_wellord2(sK1))
    | ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ v1_relat_1(k1_wellord2(sK0))
    | spl4_25 ),
    inference(resolution,[],[f281,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( r4_wellord1(X1,X0)
      | ~ v1_relat_1(X1)
      | ~ r4_wellord1(X0,X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r4_wellord1(X1,X0)
          | ~ r4_wellord1(X0,X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r4_wellord1(X0,X1)
           => r4_wellord1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).

fof(f281,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | spl4_25 ),
    inference(avatar_component_clause,[],[f279])).

fof(f279,plain,
    ( spl4_25
  <=> r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f282,plain,
    ( ~ spl4_25
    | spl4_23
    | ~ spl4_24 ),
    inference(avatar_split_clause,[],[f277,f271,f252,f279])).

fof(f252,plain,
    ( spl4_23
  <=> r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).

fof(f271,plain,
    ( spl4_24
  <=> k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f277,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))
    | spl4_23
    | ~ spl4_24 ),
    inference(superposition,[],[f254,f273])).

fof(f273,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f271])).

fof(f254,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | spl4_23 ),
    inference(avatar_component_clause,[],[f252])).

fof(f274,plain,
    ( spl4_24
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f224,f218,f271])).

fof(f218,plain,
    ( spl4_20
  <=> r1_tarski(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f224,plain,
    ( k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)
    | ~ spl4_20 ),
    inference(resolution,[],[f220,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).

fof(f220,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f218])).

fof(f261,plain,
    ( ~ spl4_10
    | spl4_22 ),
    inference(avatar_contradiction_clause,[],[f260])).

fof(f260,plain,
    ( $false
    | ~ spl4_10
    | spl4_22 ),
    inference(subsumption_resolution,[],[f259,f35])).

fof(f259,plain,
    ( ~ v1_relat_1(k1_wellord2(sK1))
    | ~ spl4_10
    | spl4_22 ),
    inference(subsumption_resolution,[],[f258,f143])).

fof(f143,plain,
    ( r2_hidden(sK0,sK1)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f142])).

fof(f142,plain,
    ( spl4_10
  <=> r2_hidden(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f258,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ v1_relat_1(k1_wellord2(sK1))
    | spl4_22 ),
    inference(superposition,[],[f250,f54])).

fof(f54,plain,(
    ! [X0] :
      ( k3_relat_1(k1_wellord2(X0)) = X0
      | ~ v1_relat_1(k1_wellord2(X0)) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k3_relat_1(X1) = X0
      | k1_wellord2(X0) != X1 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) )
              | ~ r2_hidden(X3,X0)
              | ~ r2_hidden(X2,X0) )
          & k3_relat_1(X1) = X0 ) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_wellord2(X0) = X1
      <=> ( ! [X2,X3] :
              ( ( r2_hidden(X3,X0)
                & r2_hidden(X2,X0) )
             => ( r2_hidden(k4_tarski(X2,X3),X1)
              <=> r1_tarski(X2,X3) ) )
          & k3_relat_1(X1) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).

fof(f250,plain,
    ( ~ r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1)))
    | spl4_22 ),
    inference(avatar_component_clause,[],[f248])).

fof(f248,plain,
    ( spl4_22
  <=> r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f255,plain,
    ( ~ spl4_22
    | ~ spl4_23
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f246,f142,f91,f68,f63,f252,f248])).

fof(f63,plain,
    ( spl4_1
  <=> v3_ordinal1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f68,plain,
    ( spl4_2
  <=> v3_ordinal1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f91,plain,
    ( spl4_5
  <=> v2_wellord1(k1_wellord2(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f246,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f140,f143])).

fof(f140,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1)))
    | ~ r2_hidden(sK0,sK1)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f137,f65])).

fof(f65,plain,
    ( v3_ordinal1(sK1)
    | ~ spl4_1 ),
    inference(avatar_component_clause,[],[f63])).

fof(f137,plain,
    ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))
    | ~ r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1)))
    | ~ r2_hidden(sK0,sK1)
    | ~ v3_ordinal1(sK1)
    | ~ spl4_2
    | ~ spl4_5 ),
    inference(superposition,[],[f101,f83])).

fof(f83,plain,
    ( ! [X2] :
        ( sK0 = k1_wellord1(k1_wellord2(X2),sK0)
        | ~ r2_hidden(sK0,X2)
        | ~ v3_ordinal1(X2) )
    | ~ spl4_2 ),
    inference(resolution,[],[f70,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | ~ r2_hidden(X0,X1)
      | k1_wellord1(k1_wellord2(X1),X0) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_wellord1(k1_wellord2(X1),X0) = X0
          | ~ r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r2_hidden(X0,X1)
           => k1_wellord1(k1_wellord2(X1),X0) = X0 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).

fof(f70,plain,
    ( v3_ordinal1(sK0)
    | ~ spl4_2 ),
    inference(avatar_component_clause,[],[f68])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0)))
        | ~ r2_hidden(X0,k3_relat_1(k1_wellord2(sK1))) )
    | ~ spl4_5 ),
    inference(subsumption_resolution,[],[f100,f35])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k1_wellord2(sK1))
        | ~ r2_hidden(X0,k3_relat_1(k1_wellord2(sK1)))
        | ~ r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0))) )
    | ~ spl4_5 ),
    inference(resolution,[],[f93,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0)
      | ~ r2_hidden(X1,k3_relat_1(X0))
      | ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
          | ~ r2_hidden(X1,k3_relat_1(X0)) )
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
       => ! [X1] :
            ~ ( r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))
              & r2_hidden(X1,k3_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).

fof(f93,plain,
    ( v2_wellord1(k1_wellord2(sK1))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f91])).

fof(f245,plain,
    ( ~ spl4_14
    | spl4_19 ),
    inference(avatar_split_clause,[],[f244,f205,f174])).

fof(f174,plain,
    ( spl4_14
  <=> r2_hidden(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f205,plain,
    ( spl4_19
  <=> r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f244,plain,
    ( ~ r2_hidden(sK1,sK0)
    | spl4_19 ),
    inference(subsumption_resolution,[],[f243,f35])).

fof(f243,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ v1_relat_1(k1_wellord2(sK0))
    | spl4_19 ),
    inference(superposition,[],[f207,f54])).

fof(f207,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0)))
    | spl4_19 ),
    inference(avatar_component_clause,[],[f205])).

fof(f233,plain,
    ( ~ spl4_14
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f222,f218,f174])).

fof(f222,plain,
    ( ~ r2_hidden(sK1,sK0)
    | ~ spl4_20 ),
    inference(resolution,[],[f220,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ~ ( r1_tarski(X1,X0)
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).

fof(f221,plain,
    ( spl4_20
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f216,f110,f218])).

fof(f110,plain,
    ( spl4_7
  <=> r2_xboole_0(sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f216,plain,
    ( r1_tarski(sK0,sK1)
    | ~ spl4_7 ),
    inference(resolution,[],[f112,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r2_xboole_0(X0,X1)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r2_xboole_0(X0,X1)
    <=> ( X0 != X1
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).

% (1034)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f112,plain,
    ( r2_xboole_0(sK0,sK1)
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f208,plain,
    ( ~ spl4_19
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_14
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f203,f197,f174,f96,f86,f68,f63,f205])).

fof(f96,plain,
    ( spl4_6
  <=> v2_wellord1(k1_wellord2(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f197,plain,
    ( spl4_18
  <=> k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f203,plain,
    ( ~ r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_14
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f202,f88])).

fof(f202,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))
    | ~ r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_14
    | ~ spl4_18 ),
    inference(forward_demodulation,[],[f201,f199])).

fof(f199,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f197])).

fof(f201,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0)))
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6
    | ~ spl4_14 ),
    inference(subsumption_resolution,[],[f150,f176])).

fof(f176,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f174])).

fof(f150,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0)))
    | ~ r2_hidden(sK1,sK0)
    | ~ spl4_1
    | ~ spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f147,f70])).

fof(f147,plain,
    ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1))
    | ~ r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0)))
    | ~ r2_hidden(sK1,sK0)
    | ~ v3_ordinal1(sK0)
    | ~ spl4_1
    | ~ spl4_6 ),
    inference(superposition,[],[f103,f79])).

fof(f79,plain,
    ( ! [X2] :
        ( sK1 = k1_wellord1(k1_wellord2(X2),sK1)
        | ~ r2_hidden(sK1,X2)
        | ~ v3_ordinal1(X2) )
    | ~ spl4_1 ),
    inference(resolution,[],[f65,f39])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),k1_wellord1(k1_wellord2(sK0),X0)))
        | ~ r2_hidden(X0,k3_relat_1(k1_wellord2(sK0))) )
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f102,f35])).

fof(f102,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(k1_wellord2(sK0))
        | ~ r2_hidden(X0,k3_relat_1(k1_wellord2(sK0)))
        | ~ r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),k1_wellord1(k1_wellord2(sK0),X0))) )
    | ~ spl4_6 ),
    inference(resolution,[],[f98,f36])).

fof(f98,plain,
    ( v2_wellord1(k1_wellord2(sK0))
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f96])).

fof(f200,plain,
    ( spl4_18
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f132,f126,f197])).

fof(f126,plain,
    ( spl4_9
  <=> r1_tarski(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f132,plain,
    ( k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)
    | ~ spl4_9 ),
    inference(resolution,[],[f128,f49])).

fof(f128,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f126])).

fof(f177,plain,
    ( spl4_14
    | ~ spl4_1
    | ~ spl4_2
    | spl4_3
    | spl4_10 ),
    inference(avatar_split_clause,[],[f170,f142,f73,f68,f63,f174])).

fof(f73,plain,
    ( spl4_3
  <=> sK0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f170,plain,
    ( r2_hidden(sK1,sK0)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_3
    | spl4_10 ),
    inference(subsumption_resolution,[],[f169,f75])).

fof(f75,plain,
    ( sK0 != sK1
    | spl4_3 ),
    inference(avatar_component_clause,[],[f73])).

fof(f169,plain,
    ( sK0 = sK1
    | r2_hidden(sK1,sK0)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_10 ),
    inference(subsumption_resolution,[],[f168,f65])).

fof(f168,plain,
    ( ~ v3_ordinal1(sK1)
    | sK0 = sK1
    | r2_hidden(sK1,sK0)
    | ~ spl4_2
    | spl4_10 ),
    inference(resolution,[],[f144,f81])).

fof(f81,plain,
    ( ! [X0] :
        ( r2_hidden(sK0,X0)
        | ~ v3_ordinal1(X0)
        | sK0 = X0
        | r2_hidden(X0,sK0) )
    | ~ spl4_2 ),
    inference(resolution,[],[f70,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r2_hidden(X0,X1)
      | X0 = X1
      | r2_hidden(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_hidden(X1,X0)
          | X0 = X1
          | r2_hidden(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_hidden(X1,X0)
              & X0 != X1
              & ~ r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).

fof(f144,plain,
    ( ~ r2_hidden(sK0,sK1)
    | spl4_10 ),
    inference(avatar_component_clause,[],[f142])).

fof(f145,plain,
    ( ~ spl4_10
    | ~ spl4_9 ),
    inference(avatar_split_clause,[],[f130,f126,f142])).

fof(f130,plain,
    ( ~ r2_hidden(sK0,sK1)
    | ~ spl4_9 ),
    inference(resolution,[],[f128,f53])).

fof(f129,plain,
    ( spl4_9
    | ~ spl4_8 ),
    inference(avatar_split_clause,[],[f124,f114,f126])).

fof(f114,plain,
    ( spl4_8
  <=> r2_xboole_0(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f124,plain,
    ( r1_tarski(sK1,sK0)
    | ~ spl4_8 ),
    inference(resolution,[],[f116,f50])).

fof(f116,plain,
    ( r2_xboole_0(sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f114])).

fof(f117,plain,
    ( spl4_7
    | spl4_8
    | ~ spl4_1
    | ~ spl4_2
    | spl4_3 ),
    inference(avatar_split_clause,[],[f108,f73,f68,f63,f114,f110])).

fof(f108,plain,
    ( r2_xboole_0(sK1,sK0)
    | r2_xboole_0(sK0,sK1)
    | ~ spl4_1
    | ~ spl4_2
    | spl4_3 ),
    inference(subsumption_resolution,[],[f106,f75])).

fof(f106,plain,
    ( r2_xboole_0(sK1,sK0)
    | sK0 = sK1
    | r2_xboole_0(sK0,sK1)
    | ~ spl4_1
    | ~ spl4_2 ),
    inference(resolution,[],[f78,f70])).

fof(f78,plain,
    ( ! [X1] :
        ( ~ v3_ordinal1(X1)
        | r2_xboole_0(sK1,X1)
        | sK1 = X1
        | r2_xboole_0(X1,sK1) )
    | ~ spl4_1 ),
    inference(resolution,[],[f65,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v3_ordinal1(X0)
      | ~ v3_ordinal1(X1)
      | r2_xboole_0(X0,X1)
      | X0 = X1
      | r2_xboole_0(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_xboole_0(X1,X0)
          | X0 = X1
          | r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r2_xboole_0(X1,X0)
          | X0 = X1
          | r2_xboole_0(X0,X1)
          | ~ v3_ordinal1(X1) )
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ~ ( ~ r2_xboole_0(X1,X0)
              & X0 != X1
              & ~ r2_xboole_0(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_ordinal1)).

fof(f99,plain,
    ( spl4_6
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f84,f68,f96])).

fof(f84,plain,
    ( v2_wellord1(k1_wellord2(sK0))
    | ~ spl4_2 ),
    inference(resolution,[],[f70,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v3_ordinal1(X0)
      | v2_wellord1(k1_wellord2(X0)) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v2_wellord1(k1_wellord2(X0))
      | ~ v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => v2_wellord1(k1_wellord2(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).

fof(f94,plain,
    ( spl4_5
    | ~ spl4_1 ),
    inference(avatar_split_clause,[],[f80,f63,f91])).

fof(f80,plain,
    ( v2_wellord1(k1_wellord2(sK1))
    | ~ spl4_1 ),
    inference(resolution,[],[f65,f38])).

fof(f89,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f32,f86])).

fof(f32,plain,(
    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( X0 != X1
          & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
          & v3_ordinal1(X1) )
      & v3_ordinal1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( v3_ordinal1(X0)
       => ! [X1] :
            ( v3_ordinal1(X1)
           => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
             => X0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( v3_ordinal1(X0)
     => ! [X1] :
          ( v3_ordinal1(X1)
         => ( r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).

fof(f76,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f33,f73])).

fof(f33,plain,(
    sK0 != sK1 ),
    inference(cnf_transformation,[],[f15])).

fof(f71,plain,(
    spl4_2 ),
    inference(avatar_split_clause,[],[f34,f68])).

fof(f34,plain,(
    v3_ordinal1(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f66,plain,(
    spl4_1 ),
    inference(avatar_split_clause,[],[f31,f63])).

fof(f31,plain,(
    v3_ordinal1(sK1) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:41:55 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (1028)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.48  % (1028)Refutation found. Thanks to Tanya!
% 0.22/0.48  % SZS status Theorem for theBenchmark
% 0.22/0.48  % (1044)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.48  % SZS output start Proof for theBenchmark
% 0.22/0.48  fof(f298,plain,(
% 0.22/0.48    $false),
% 0.22/0.48    inference(avatar_sat_refutation,[],[f66,f71,f76,f89,f94,f99,f117,f129,f145,f177,f200,f208,f221,f233,f245,f255,f261,f274,f282,f297])).
% 0.22/0.49  fof(f297,plain,(
% 0.22/0.49    ~spl4_4 | spl4_25),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f296])).
% 0.22/0.49  fof(f296,plain,(
% 0.22/0.49    $false | (~spl4_4 | spl4_25)),
% 0.22/0.49    inference(subsumption_resolution,[],[f295,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ( ! [X0] : (v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : v1_relat_1(k1_wellord2(X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_wellord2)).
% 0.22/0.49  fof(f295,plain,(
% 0.22/0.49    ~v1_relat_1(k1_wellord2(sK0)) | (~spl4_4 | spl4_25)),
% 0.22/0.49    inference(subsumption_resolution,[],[f294,f88])).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~spl4_4),
% 0.22/0.49    inference(avatar_component_clause,[],[f86])).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    spl4_4 <=> r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.49  fof(f294,plain,(
% 0.22/0.49    ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~v1_relat_1(k1_wellord2(sK0)) | spl4_25),
% 0.22/0.49    inference(subsumption_resolution,[],[f293,f35])).
% 0.22/0.49  fof(f293,plain,(
% 0.22/0.49    ~v1_relat_1(k1_wellord2(sK1)) | ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~v1_relat_1(k1_wellord2(sK0)) | spl4_25),
% 0.22/0.49    inference(resolution,[],[f281,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    ( ! [X0,X1] : (r4_wellord1(X1,X0) | ~v1_relat_1(X1) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((r4_wellord1(X1,X0) | ~r4_wellord1(X0,X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r4_wellord1(X0,X1) => r4_wellord1(X1,X0))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_wellord1)).
% 0.22/0.49  fof(f281,plain,(
% 0.22/0.49    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | spl4_25),
% 0.22/0.49    inference(avatar_component_clause,[],[f279])).
% 0.22/0.49  fof(f279,plain,(
% 0.22/0.49    spl4_25 <=> r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.22/0.49  fof(f282,plain,(
% 0.22/0.49    ~spl4_25 | spl4_23 | ~spl4_24),
% 0.22/0.49    inference(avatar_split_clause,[],[f277,f271,f252,f279])).
% 0.22/0.49  fof(f252,plain,(
% 0.22/0.49    spl4_23 <=> r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_23])])).
% 0.22/0.49  fof(f271,plain,(
% 0.22/0.49    spl4_24 <=> k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.22/0.49  fof(f277,plain,(
% 0.22/0.49    ~r4_wellord1(k1_wellord2(sK1),k1_wellord2(sK0)) | (spl4_23 | ~spl4_24)),
% 0.22/0.49    inference(superposition,[],[f254,f273])).
% 0.22/0.49  fof(f273,plain,(
% 0.22/0.49    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) | ~spl4_24),
% 0.22/0.49    inference(avatar_component_clause,[],[f271])).
% 0.22/0.49  fof(f254,plain,(
% 0.22/0.49    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | spl4_23),
% 0.22/0.49    inference(avatar_component_clause,[],[f252])).
% 0.22/0.49  fof(f274,plain,(
% 0.22/0.49    spl4_24 | ~spl4_20),
% 0.22/0.49    inference(avatar_split_clause,[],[f224,f218,f271])).
% 0.22/0.49  fof(f218,plain,(
% 0.22/0.49    spl4_20 <=> r1_tarski(sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.22/0.49  fof(f224,plain,(
% 0.22/0.49    k1_wellord2(sK0) = k2_wellord1(k1_wellord2(sK1),sK0) | ~spl4_20),
% 0.22/0.49    inference(resolution,[],[f220,f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0,X1] : (k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0) | ~r1_tarski(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,axiom,(
% 0.22/0.49    ! [X0,X1] : (r1_tarski(X0,X1) => k1_wellord2(X0) = k2_wellord1(k1_wellord2(X1),X0))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_wellord2)).
% 0.22/0.49  fof(f220,plain,(
% 0.22/0.49    r1_tarski(sK0,sK1) | ~spl4_20),
% 0.22/0.49    inference(avatar_component_clause,[],[f218])).
% 0.22/0.49  fof(f261,plain,(
% 0.22/0.49    ~spl4_10 | spl4_22),
% 0.22/0.49    inference(avatar_contradiction_clause,[],[f260])).
% 0.22/0.49  fof(f260,plain,(
% 0.22/0.49    $false | (~spl4_10 | spl4_22)),
% 0.22/0.49    inference(subsumption_resolution,[],[f259,f35])).
% 0.22/0.49  fof(f259,plain,(
% 0.22/0.49    ~v1_relat_1(k1_wellord2(sK1)) | (~spl4_10 | spl4_22)),
% 0.22/0.49    inference(subsumption_resolution,[],[f258,f143])).
% 0.22/0.49  fof(f143,plain,(
% 0.22/0.49    r2_hidden(sK0,sK1) | ~spl4_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f142])).
% 0.22/0.49  fof(f142,plain,(
% 0.22/0.49    spl4_10 <=> r2_hidden(sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.49  fof(f258,plain,(
% 0.22/0.49    ~r2_hidden(sK0,sK1) | ~v1_relat_1(k1_wellord2(sK1)) | spl4_22),
% 0.22/0.49    inference(superposition,[],[f250,f54])).
% 0.22/0.49  fof(f54,plain,(
% 0.22/0.49    ( ! [X0] : (k3_relat_1(k1_wellord2(X0)) = X0 | ~v1_relat_1(k1_wellord2(X0))) )),
% 0.22/0.49    inference(equality_resolution,[],[f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v1_relat_1(X1) | k3_relat_1(X1) = X0 | k1_wellord2(X0) != X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | ~r2_hidden(X3,X0) | ~r2_hidden(X2,X0)) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(flattening,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0,X1] : ((k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3)) | (~r2_hidden(X3,X0) | ~r2_hidden(X2,X0))) & k3_relat_1(X1) = X0)) | ~v1_relat_1(X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0,X1] : (v1_relat_1(X1) => (k1_wellord2(X0) = X1 <=> (! [X2,X3] : ((r2_hidden(X3,X0) & r2_hidden(X2,X0)) => (r2_hidden(k4_tarski(X2,X3),X1) <=> r1_tarski(X2,X3))) & k3_relat_1(X1) = X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_wellord2)).
% 0.22/0.49  fof(f250,plain,(
% 0.22/0.49    ~r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1))) | spl4_22),
% 0.22/0.49    inference(avatar_component_clause,[],[f248])).
% 0.22/0.49  fof(f248,plain,(
% 0.22/0.49    spl4_22 <=> r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 0.22/0.49  fof(f255,plain,(
% 0.22/0.49    ~spl4_22 | ~spl4_23 | ~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f246,f142,f91,f68,f63,f252,f248])).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    spl4_1 <=> v3_ordinal1(sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    spl4_2 <=> v3_ordinal1(sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.49  fof(f91,plain,(
% 0.22/0.49    spl4_5 <=> v2_wellord1(k1_wellord2(sK1))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 0.22/0.49  fof(f246,plain,(
% 0.22/0.49    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1))) | (~spl4_1 | ~spl4_2 | ~spl4_5 | ~spl4_10)),
% 0.22/0.49    inference(subsumption_resolution,[],[f140,f143])).
% 0.22/0.49  fof(f140,plain,(
% 0.22/0.49    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1))) | ~r2_hidden(sK0,sK1) | (~spl4_1 | ~spl4_2 | ~spl4_5)),
% 0.22/0.49    inference(subsumption_resolution,[],[f137,f65])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    v3_ordinal1(sK1) | ~spl4_1),
% 0.22/0.49    inference(avatar_component_clause,[],[f63])).
% 0.22/0.49  fof(f137,plain,(
% 0.22/0.49    ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),sK0)) | ~r2_hidden(sK0,k3_relat_1(k1_wellord2(sK1))) | ~r2_hidden(sK0,sK1) | ~v3_ordinal1(sK1) | (~spl4_2 | ~spl4_5)),
% 0.22/0.49    inference(superposition,[],[f101,f83])).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    ( ! [X2] : (sK0 = k1_wellord1(k1_wellord2(X2),sK0) | ~r2_hidden(sK0,X2) | ~v3_ordinal1(X2)) ) | ~spl4_2),
% 0.22/0.49    inference(resolution,[],[f70,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | ~r2_hidden(X0,X1) | k1_wellord1(k1_wellord2(X1),X0) = X0) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.49    inference(flattening,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((k1_wellord1(k1_wellord2(X1),X0) = X0 | ~r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r2_hidden(X0,X1) => k1_wellord1(k1_wellord2(X1),X0) = X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_wellord2)).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    v3_ordinal1(sK0) | ~spl4_2),
% 0.22/0.49    inference(avatar_component_clause,[],[f68])).
% 0.22/0.49  fof(f101,plain,(
% 0.22/0.49    ( ! [X0] : (~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0))) | ~r2_hidden(X0,k3_relat_1(k1_wellord2(sK1)))) ) | ~spl4_5),
% 0.22/0.49    inference(subsumption_resolution,[],[f100,f35])).
% 0.22/0.49  fof(f100,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_relat_1(k1_wellord2(sK1)) | ~r2_hidden(X0,k3_relat_1(k1_wellord2(sK1))) | ~r4_wellord1(k1_wellord2(sK1),k2_wellord1(k1_wellord2(sK1),k1_wellord1(k1_wellord2(sK1),X0)))) ) | ~spl4_5),
% 0.22/0.49    inference(resolution,[],[f93,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v2_wellord1(X0) | ~v1_relat_1(X0) | ~r2_hidden(X1,k3_relat_1(X0)) | ~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1)))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(flattening,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : ((! [X1] : (~r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) | ~r2_hidden(X1,k3_relat_1(X0))) | ~v2_wellord1(X0)) | ~v1_relat_1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : (v1_relat_1(X0) => (v2_wellord1(X0) => ! [X1] : ~(r4_wellord1(X0,k2_wellord1(X0,k1_wellord1(X0,X1))) & r2_hidden(X1,k3_relat_1(X0)))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_wellord1)).
% 0.22/0.49  fof(f93,plain,(
% 0.22/0.49    v2_wellord1(k1_wellord2(sK1)) | ~spl4_5),
% 0.22/0.49    inference(avatar_component_clause,[],[f91])).
% 0.22/0.49  fof(f245,plain,(
% 0.22/0.49    ~spl4_14 | spl4_19),
% 0.22/0.49    inference(avatar_split_clause,[],[f244,f205,f174])).
% 0.22/0.49  fof(f174,plain,(
% 0.22/0.49    spl4_14 <=> r2_hidden(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.49  fof(f205,plain,(
% 0.22/0.49    spl4_19 <=> r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0)))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 0.22/0.49  fof(f244,plain,(
% 0.22/0.49    ~r2_hidden(sK1,sK0) | spl4_19),
% 0.22/0.49    inference(subsumption_resolution,[],[f243,f35])).
% 0.22/0.49  fof(f243,plain,(
% 0.22/0.49    ~r2_hidden(sK1,sK0) | ~v1_relat_1(k1_wellord2(sK0)) | spl4_19),
% 0.22/0.49    inference(superposition,[],[f207,f54])).
% 0.22/0.49  fof(f207,plain,(
% 0.22/0.49    ~r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0))) | spl4_19),
% 0.22/0.49    inference(avatar_component_clause,[],[f205])).
% 0.22/0.49  fof(f233,plain,(
% 0.22/0.49    ~spl4_14 | ~spl4_20),
% 0.22/0.49    inference(avatar_split_clause,[],[f222,f218,f174])).
% 0.22/0.49  fof(f222,plain,(
% 0.22/0.49    ~r2_hidden(sK1,sK0) | ~spl4_20),
% 0.22/0.49    inference(resolution,[],[f220,f53])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0,X1] : (~r1_tarski(X1,X0) | ~r2_hidden(X0,X1))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0,X1] : ~(r1_tarski(X1,X0) & r2_hidden(X0,X1))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_ordinal1)).
% 0.22/0.49  fof(f221,plain,(
% 0.22/0.49    spl4_20 | ~spl4_7),
% 0.22/0.49    inference(avatar_split_clause,[],[f216,f110,f218])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    spl4_7 <=> r2_xboole_0(sK0,sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.49  fof(f216,plain,(
% 0.22/0.49    r1_tarski(sK0,sK1) | ~spl4_7),
% 0.22/0.49    inference(resolution,[],[f112,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~r2_xboole_0(X0,X1) | r1_tarski(X0,X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0,X1] : (r2_xboole_0(X0,X1) <=> (X0 != X1 & r1_tarski(X0,X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d8_xboole_0)).
% 0.22/0.49  % (1034)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.49  fof(f112,plain,(
% 0.22/0.49    r2_xboole_0(sK0,sK1) | ~spl4_7),
% 0.22/0.49    inference(avatar_component_clause,[],[f110])).
% 0.22/0.49  fof(f208,plain,(
% 0.22/0.49    ~spl4_19 | ~spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_14 | ~spl4_18),
% 0.22/0.49    inference(avatar_split_clause,[],[f203,f197,f174,f96,f86,f68,f63,f205])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    spl4_6 <=> v2_wellord1(k1_wellord2(sK0))),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.49  fof(f197,plain,(
% 0.22/0.49    spl4_18 <=> k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.49  fof(f203,plain,(
% 0.22/0.49    ~r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0))) | (~spl4_1 | ~spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_14 | ~spl4_18)),
% 0.22/0.49    inference(subsumption_resolution,[],[f202,f88])).
% 0.22/0.49  fof(f202,plain,(
% 0.22/0.49    ~r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1)) | ~r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0))) | (~spl4_1 | ~spl4_2 | ~spl4_6 | ~spl4_14 | ~spl4_18)),
% 0.22/0.49    inference(forward_demodulation,[],[f201,f199])).
% 0.22/0.49  fof(f199,plain,(
% 0.22/0.49    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | ~spl4_18),
% 0.22/0.49    inference(avatar_component_clause,[],[f197])).
% 0.22/0.49  fof(f201,plain,(
% 0.22/0.49    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0))) | (~spl4_1 | ~spl4_2 | ~spl4_6 | ~spl4_14)),
% 0.22/0.49    inference(subsumption_resolution,[],[f150,f176])).
% 0.22/0.49  fof(f176,plain,(
% 0.22/0.49    r2_hidden(sK1,sK0) | ~spl4_14),
% 0.22/0.49    inference(avatar_component_clause,[],[f174])).
% 0.22/0.49  fof(f150,plain,(
% 0.22/0.49    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0))) | ~r2_hidden(sK1,sK0) | (~spl4_1 | ~spl4_2 | ~spl4_6)),
% 0.22/0.49    inference(subsumption_resolution,[],[f147,f70])).
% 0.22/0.49  fof(f147,plain,(
% 0.22/0.49    ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),sK1)) | ~r2_hidden(sK1,k3_relat_1(k1_wellord2(sK0))) | ~r2_hidden(sK1,sK0) | ~v3_ordinal1(sK0) | (~spl4_1 | ~spl4_6)),
% 0.22/0.49    inference(superposition,[],[f103,f79])).
% 0.22/0.49  fof(f79,plain,(
% 0.22/0.49    ( ! [X2] : (sK1 = k1_wellord1(k1_wellord2(X2),sK1) | ~r2_hidden(sK1,X2) | ~v3_ordinal1(X2)) ) | ~spl4_1),
% 0.22/0.49    inference(resolution,[],[f65,f39])).
% 0.22/0.49  fof(f103,plain,(
% 0.22/0.49    ( ! [X0] : (~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),k1_wellord1(k1_wellord2(sK0),X0))) | ~r2_hidden(X0,k3_relat_1(k1_wellord2(sK0)))) ) | ~spl4_6),
% 0.22/0.49    inference(subsumption_resolution,[],[f102,f35])).
% 0.22/0.49  fof(f102,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_relat_1(k1_wellord2(sK0)) | ~r2_hidden(X0,k3_relat_1(k1_wellord2(sK0))) | ~r4_wellord1(k1_wellord2(sK0),k2_wellord1(k1_wellord2(sK0),k1_wellord1(k1_wellord2(sK0),X0)))) ) | ~spl4_6),
% 0.22/0.49    inference(resolution,[],[f98,f36])).
% 0.22/0.49  fof(f98,plain,(
% 0.22/0.49    v2_wellord1(k1_wellord2(sK0)) | ~spl4_6),
% 0.22/0.49    inference(avatar_component_clause,[],[f96])).
% 0.22/0.49  fof(f200,plain,(
% 0.22/0.49    spl4_18 | ~spl4_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f132,f126,f197])).
% 0.22/0.49  fof(f126,plain,(
% 0.22/0.49    spl4_9 <=> r1_tarski(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.49  fof(f132,plain,(
% 0.22/0.49    k1_wellord2(sK1) = k2_wellord1(k1_wellord2(sK0),sK1) | ~spl4_9),
% 0.22/0.49    inference(resolution,[],[f128,f49])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    r1_tarski(sK1,sK0) | ~spl4_9),
% 0.22/0.49    inference(avatar_component_clause,[],[f126])).
% 0.22/0.49  fof(f177,plain,(
% 0.22/0.49    spl4_14 | ~spl4_1 | ~spl4_2 | spl4_3 | spl4_10),
% 0.22/0.49    inference(avatar_split_clause,[],[f170,f142,f73,f68,f63,f174])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    spl4_3 <=> sK0 = sK1),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.49  fof(f170,plain,(
% 0.22/0.49    r2_hidden(sK1,sK0) | (~spl4_1 | ~spl4_2 | spl4_3 | spl4_10)),
% 0.22/0.49    inference(subsumption_resolution,[],[f169,f75])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    sK0 != sK1 | spl4_3),
% 0.22/0.49    inference(avatar_component_clause,[],[f73])).
% 0.22/0.49  fof(f169,plain,(
% 0.22/0.49    sK0 = sK1 | r2_hidden(sK1,sK0) | (~spl4_1 | ~spl4_2 | spl4_10)),
% 0.22/0.49    inference(subsumption_resolution,[],[f168,f65])).
% 0.22/0.49  fof(f168,plain,(
% 0.22/0.49    ~v3_ordinal1(sK1) | sK0 = sK1 | r2_hidden(sK1,sK0) | (~spl4_2 | spl4_10)),
% 0.22/0.49    inference(resolution,[],[f144,f81])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    ( ! [X0] : (r2_hidden(sK0,X0) | ~v3_ordinal1(X0) | sK0 = X0 | r2_hidden(X0,sK0)) ) | ~spl4_2),
% 0.22/0.49    inference(resolution,[],[f70,f41])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r2_hidden(X0,X1) | X0 = X1 | r2_hidden(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.49    inference(flattening,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((r2_hidden(X1,X0) | X0 = X1 | r2_hidden(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_hidden(X1,X0) & X0 != X1 & ~r2_hidden(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_ordinal1)).
% 0.22/0.49  fof(f144,plain,(
% 0.22/0.49    ~r2_hidden(sK0,sK1) | spl4_10),
% 0.22/0.49    inference(avatar_component_clause,[],[f142])).
% 0.22/0.49  fof(f145,plain,(
% 0.22/0.49    ~spl4_10 | ~spl4_9),
% 0.22/0.49    inference(avatar_split_clause,[],[f130,f126,f142])).
% 0.22/0.49  fof(f130,plain,(
% 0.22/0.49    ~r2_hidden(sK0,sK1) | ~spl4_9),
% 0.22/0.49    inference(resolution,[],[f128,f53])).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    spl4_9 | ~spl4_8),
% 0.22/0.49    inference(avatar_split_clause,[],[f124,f114,f126])).
% 0.22/0.49  fof(f114,plain,(
% 0.22/0.49    spl4_8 <=> r2_xboole_0(sK1,sK0)),
% 0.22/0.49    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    r1_tarski(sK1,sK0) | ~spl4_8),
% 0.22/0.49    inference(resolution,[],[f116,f50])).
% 0.22/0.49  fof(f116,plain,(
% 0.22/0.49    r2_xboole_0(sK1,sK0) | ~spl4_8),
% 0.22/0.49    inference(avatar_component_clause,[],[f114])).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    spl4_7 | spl4_8 | ~spl4_1 | ~spl4_2 | spl4_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f108,f73,f68,f63,f114,f110])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    r2_xboole_0(sK1,sK0) | r2_xboole_0(sK0,sK1) | (~spl4_1 | ~spl4_2 | spl4_3)),
% 0.22/0.49    inference(subsumption_resolution,[],[f106,f75])).
% 0.22/0.49  fof(f106,plain,(
% 0.22/0.49    r2_xboole_0(sK1,sK0) | sK0 = sK1 | r2_xboole_0(sK0,sK1) | (~spl4_1 | ~spl4_2)),
% 0.22/0.49    inference(resolution,[],[f78,f70])).
% 0.22/0.49  fof(f78,plain,(
% 0.22/0.49    ( ! [X1] : (~v3_ordinal1(X1) | r2_xboole_0(sK1,X1) | sK1 = X1 | r2_xboole_0(X1,sK1)) ) | ~spl4_1),
% 0.22/0.49    inference(resolution,[],[f65,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~v3_ordinal1(X0) | ~v3_ordinal1(X1) | r2_xboole_0(X0,X1) | X0 = X1 | r2_xboole_0(X1,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (r2_xboole_0(X1,X0) | X0 = X1 | r2_xboole_0(X0,X1) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.49    inference(flattening,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((r2_xboole_0(X1,X0) | X0 = X1 | r2_xboole_0(X0,X1)) | ~v3_ordinal1(X1)) | ~v3_ordinal1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => ~(~r2_xboole_0(X1,X0) & X0 != X1 & ~r2_xboole_0(X0,X1))))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_ordinal1)).
% 0.22/0.49  fof(f99,plain,(
% 0.22/0.49    spl4_6 | ~spl4_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f84,f68,f96])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    v2_wellord1(k1_wellord2(sK0)) | ~spl4_2),
% 0.22/0.49    inference(resolution,[],[f70,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    ( ! [X0] : (~v3_ordinal1(X0) | v2_wellord1(k1_wellord2(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (v2_wellord1(k1_wellord2(X0)) | ~v3_ordinal1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f10])).
% 0.22/0.49  fof(f10,axiom,(
% 0.22/0.49    ! [X0] : (v3_ordinal1(X0) => v2_wellord1(k1_wellord2(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_wellord2)).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    spl4_5 | ~spl4_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f80,f63,f91])).
% 0.22/0.49  fof(f80,plain,(
% 0.22/0.49    v2_wellord1(k1_wellord2(sK1)) | ~spl4_1),
% 0.22/0.49    inference(resolution,[],[f65,f38])).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    spl4_4),
% 0.22/0.49    inference(avatar_split_clause,[],[f32,f86])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    r4_wellord1(k1_wellord2(sK0),k1_wellord2(sK1))),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : (X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.49    inference(flattening,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : ((X0 != X1 & r4_wellord1(k1_wellord2(X0),k1_wellord2(X1))) & v3_ordinal1(X1)) & v3_ordinal1(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f13])).
% 0.22/0.49  fof(f13,negated_conjecture,(
% 0.22/0.49    ~! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.22/0.49    inference(negated_conjecture,[],[f12])).
% 0.22/0.49  fof(f12,conjecture,(
% 0.22/0.49    ! [X0] : (v3_ordinal1(X0) => ! [X1] : (v3_ordinal1(X1) => (r4_wellord1(k1_wellord2(X0),k1_wellord2(X1)) => X0 = X1)))),
% 0.22/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_wellord2)).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    ~spl4_3),
% 0.22/0.49    inference(avatar_split_clause,[],[f33,f73])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    sK0 != sK1),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    spl4_2),
% 0.22/0.49    inference(avatar_split_clause,[],[f34,f68])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    v3_ordinal1(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    spl4_1),
% 0.22/0.49    inference(avatar_split_clause,[],[f31,f63])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    v3_ordinal1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (1028)------------------------------
% 0.22/0.49  % (1028)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (1028)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (1028)Memory used [KB]: 10746
% 0.22/0.49  % (1028)Time elapsed: 0.069 s
% 0.22/0.49  % (1028)------------------------------
% 0.22/0.49  % (1028)------------------------------
% 0.22/0.49  % (1024)Success in time 0.13 s
%------------------------------------------------------------------------------
