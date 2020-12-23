%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 12:48:28 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  128 ( 199 expanded)
%              Number of leaves         :   35 (  90 expanded)
%              Depth                    :    9
%              Number of atoms          :  374 ( 604 expanded)
%              Number of equality atoms :   50 (  92 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f528,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f65,f74,f76,f80,f84,f89,f102,f110,f114,f126,f130,f141,f145,f175,f183,f187,f211,f259,f378,f414,f432,f472,f511,f527])).

fof(f527,plain,
    ( ~ spl3_29
    | ~ spl3_47
    | ~ spl3_48
    | ~ spl3_49 ),
    inference(avatar_contradiction_clause,[],[f526])).

fof(f526,plain,
    ( $false
    | ~ spl3_29
    | ~ spl3_47
    | ~ spl3_48
    | ~ spl3_49 ),
    inference(subsumption_resolution,[],[f471,f512])).

fof(f512,plain,
    ( ~ r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(sK1))
    | ~ spl3_29
    | ~ spl3_47
    | ~ spl3_49 ),
    inference(unit_resulting_resolution,[],[f210,f413,f510])).

fof(f510,plain,
    ( ! [X2] :
        ( ~ r2_hidden(X2,k1_relat_1(sK1))
        | ~ r2_hidden(X2,sK0)
        | r2_hidden(X2,k1_xboole_0) )
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f509])).

fof(f509,plain,
    ( spl3_49
  <=> ! [X2] :
        ( r2_hidden(X2,k1_xboole_0)
        | ~ r2_hidden(X2,sK0)
        | ~ r2_hidden(X2,k1_relat_1(sK1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f413,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0),sK0)
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f411])).

fof(f411,plain,
    ( spl3_47
  <=> r2_hidden(sK2(k1_relat_1(sK1),sK0),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f210,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f209])).

fof(f209,plain,
    ( spl3_29
  <=> ! [X0] : ~ r2_hidden(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f471,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(sK1))
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f469])).

fof(f469,plain,
    ( spl3_48
  <=> r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f511,plain,
    ( ~ spl3_1
    | spl3_49
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f395,f185,f86,f67,f509,f62])).

fof(f62,plain,
    ( spl3_1
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f67,plain,
    ( spl3_2
  <=> k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f86,plain,
    ( spl3_6
  <=> k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f185,plain,
    ( spl3_26
  <=> ! [X1,X0,X2] :
        ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,X1)
        | ~ v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f395,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k1_xboole_0)
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | ~ r2_hidden(X2,sK0)
        | ~ v1_relat_1(sK1) )
    | ~ spl3_2
    | ~ spl3_6
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f387,f88])).

fof(f88,plain,
    ( k1_xboole_0 = k1_relat_1(k1_xboole_0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f86])).

fof(f387,plain,
    ( ! [X2] :
        ( r2_hidden(X2,k1_relat_1(k1_xboole_0))
        | ~ r2_hidden(X2,k1_relat_1(sK1))
        | ~ r2_hidden(X2,sK0)
        | ~ v1_relat_1(sK1) )
    | ~ spl3_2
    | ~ spl3_26 ),
    inference(superposition,[],[f186,f69])).

fof(f69,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f186,plain,
    ( ! [X2,X0,X1] :
        ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
        | ~ r2_hidden(X0,k1_relat_1(X2))
        | ~ r2_hidden(X0,X1)
        | ~ v1_relat_1(X2) )
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f185])).

fof(f472,plain,
    ( spl3_48
    | spl3_3
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f383,f124,f71,f469])).

fof(f71,plain,
    ( spl3_3
  <=> r1_xboole_0(k1_relat_1(sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f124,plain,
    ( spl3_14
  <=> ! [X1,X0] :
        ( r2_hidden(sK2(X0,X1),X0)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f383,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(sK1))
    | spl3_3
    | ~ spl3_14 ),
    inference(unit_resulting_resolution,[],[f72,f125])).

fof(f125,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1),X0)
        | r1_xboole_0(X0,X1) )
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f124])).

fof(f72,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f432,plain,
    ( spl3_2
    | ~ spl3_25
    | ~ spl3_46 ),
    inference(avatar_contradiction_clause,[],[f431])).

fof(f431,plain,
    ( $false
    | spl3_2
    | ~ spl3_25
    | ~ spl3_46 ),
    inference(subsumption_resolution,[],[f68,f427])).

fof(f427,plain,
    ( k1_xboole_0 = k7_relat_1(sK1,sK0)
    | ~ spl3_25
    | ~ spl3_46 ),
    inference(superposition,[],[f377,f182])).

fof(f182,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f181])).

fof(f181,plain,
    ( spl3_25
  <=> ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f377,plain,
    ( k1_xboole_0 = k5_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f375])).

fof(f375,plain,
    ( spl3_46
  <=> k1_xboole_0 = k5_relat_1(k6_relat_1(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f68,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f67])).

fof(f414,plain,
    ( spl3_47
    | spl3_3
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f382,f128,f71,f411])).

fof(f128,plain,
    ( spl3_15
  <=> ! [X1,X0] :
        ( r2_hidden(sK2(X0,X1),X1)
        | r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f382,plain,
    ( r2_hidden(sK2(k1_relat_1(sK1),sK0),sK0)
    | spl3_3
    | ~ spl3_15 ),
    inference(unit_resulting_resolution,[],[f72,f129])).

fof(f129,plain,
    ( ! [X0,X1] :
        ( r2_hidden(sK2(X0,X1),X1)
        | r1_xboole_0(X0,X1) )
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f128])).

fof(f378,plain,
    ( spl3_46
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_17
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f262,f257,f138,f78,f62,f375])).

fof(f78,plain,
    ( spl3_4
  <=> ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f138,plain,
    ( spl3_17
  <=> r1_xboole_0(sK0,k1_relat_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f257,plain,
    ( spl3_37
  <=> ! [X1,X2] :
        ( ~ r1_xboole_0(X1,k1_relat_1(X2))
        | k1_xboole_0 = k5_relat_1(k6_relat_1(X1),X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(k6_relat_1(X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f262,plain,
    ( k1_xboole_0 = k5_relat_1(k6_relat_1(sK0),sK1)
    | ~ spl3_1
    | ~ spl3_4
    | ~ spl3_17
    | ~ spl3_37 ),
    inference(unit_resulting_resolution,[],[f64,f79,f140,f258])).

fof(f258,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 = k5_relat_1(k6_relat_1(X1),X2)
        | ~ r1_xboole_0(X1,k1_relat_1(X2))
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(k6_relat_1(X1)) )
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f257])).

fof(f140,plain,
    ( r1_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f138])).

fof(f79,plain,
    ( ! [X0] : v1_relat_1(k6_relat_1(X0))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f78])).

fof(f64,plain,
    ( v1_relat_1(sK1)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f259,plain,
    ( spl3_37
    | ~ spl3_9
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f189,f173,f100,f257])).

fof(f100,plain,
    ( spl3_9
  <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f173,plain,
    ( spl3_23
  <=> ! [X1,X0] :
        ( k1_xboole_0 = k5_relat_1(X0,X1)
        | ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f189,plain,
    ( ! [X2,X1] :
        ( ~ r1_xboole_0(X1,k1_relat_1(X2))
        | k1_xboole_0 = k5_relat_1(k6_relat_1(X1),X2)
        | ~ v1_relat_1(X2)
        | ~ v1_relat_1(k6_relat_1(X1)) )
    | ~ spl3_9
    | ~ spl3_23 ),
    inference(superposition,[],[f174,f101])).

fof(f101,plain,
    ( ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f174,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
        | k1_xboole_0 = k5_relat_1(X0,X1)
        | ~ v1_relat_1(X1)
        | ~ v1_relat_1(X0) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f173])).

fof(f211,plain,
    ( spl3_29
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f131,f112,f82,f209])).

fof(f82,plain,
    ( spl3_5
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f112,plain,
    ( spl3_12
  <=> ! [X1,X0] :
        ( ~ r2_hidden(X0,X1)
        | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f131,plain,
    ( ! [X0] : ~ r2_hidden(X0,k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(unit_resulting_resolution,[],[f83,f113])).

fof(f113,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(k1_tarski(X0),X1)
        | ~ r2_hidden(X0,X1) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f112])).

fof(f83,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f82])).

fof(f187,plain,(
    spl3_26 ),
    inference(avatar_split_clause,[],[f57,f185])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      | ~ r2_hidden(X0,k1_relat_1(X2))
      | ~ r2_hidden(X0,X1)
      | ~ v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
          | ~ r2_hidden(X0,k1_relat_1(X2))
          | ~ r2_hidden(X0,X1) )
        & ( ( r2_hidden(X0,k1_relat_1(X2))
            & r2_hidden(X0,X1) )
          | ~ r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) )
      | ~ v1_relat_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
     => ( r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1)))
      <=> ( r2_hidden(X0,k1_relat_1(X2))
          & r2_hidden(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).

fof(f183,plain,
    ( spl3_25
    | ~ spl3_1
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f156,f143,f62,f181])).

fof(f143,plain,
    ( spl3_18
  <=> ! [X1,X0] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f156,plain,
    ( ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)
    | ~ spl3_1
    | ~ spl3_18 ),
    inference(unit_resulting_resolution,[],[f64,f144])).

fof(f144,plain,
    ( ! [X0,X1] :
        ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
        | ~ v1_relat_1(X1) )
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f143])).

fof(f175,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f46,f173])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k5_relat_1(X0,X1)
      | ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k5_relat_1(X0,X1)
          | ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k5_relat_1(X0,X1)
          | ~ r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))
           => k1_xboole_0 = k5_relat_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_relat_1)).

fof(f145,plain,(
    spl3_18 ),
    inference(avatar_split_clause,[],[f51,f143])).

fof(f51,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f141,plain,
    ( spl3_17
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f115,f108,f71,f138])).

fof(f108,plain,
    ( spl3_11
  <=> ! [X1,X0] :
        ( r1_xboole_0(X1,X0)
        | ~ r1_xboole_0(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f115,plain,
    ( r1_xboole_0(sK0,k1_relat_1(sK1))
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(unit_resulting_resolution,[],[f73,f109])).

fof(f109,plain,
    ( ! [X0,X1] :
        ( ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X1,X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f73,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f71])).

fof(f130,plain,(
    spl3_15 ),
    inference(avatar_split_clause,[],[f49,f128])).

fof(f49,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X1)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ( r2_hidden(sK2(X0,X1),X1)
          & r2_hidden(sK2(X0,X1),X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f32])).

fof(f32,plain,(
    ! [X1,X0] :
      ( ? [X3] :
          ( r2_hidden(X3,X1)
          & r2_hidden(X3,X0) )
     => ( r2_hidden(sK2(X0,X1),X1)
        & r2_hidden(sK2(X0,X1),X0) ) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( ~ r1_xboole_0(X0,X1)
        | ! [X2] :
            ( ~ r2_hidden(X2,X1)
            | ~ r2_hidden(X2,X0) ) )
      & ( ? [X3] :
            ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) )
        | r1_xboole_0(X0,X1) ) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X3] :
              ~ ( r2_hidden(X3,X1)
                & r2_hidden(X3,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    inference(rectify,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ~ ( r1_xboole_0(X0,X1)
          & ? [X2] :
              ( r2_hidden(X2,X1)
              & r2_hidden(X2,X0) ) )
      & ~ ( ! [X2] :
              ~ ( r2_hidden(X2,X1)
                & r2_hidden(X2,X0) )
          & ~ r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

fof(f126,plain,(
    spl3_14 ),
    inference(avatar_split_clause,[],[f48,f124])).

fof(f48,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK2(X0,X1),X0)
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f114,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f53,f112])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ r1_xboole_0(k1_tarski(X0),X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ~ ( r2_hidden(X0,X1)
        & r1_xboole_0(k1_tarski(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

fof(f110,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f52,f108])).

fof(f52,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f102,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f45,f100])).

fof(f45,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f89,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f39,f86])).

fof(f39,plain,(
    k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    & k1_xboole_0 = k1_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

fof(f84,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f42,f82])).

fof(f42,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f80,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f41,f78])).

fof(f41,plain,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : v1_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).

fof(f76,plain,
    ( ~ spl3_2
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f75,f71,f67])).

fof(f75,plain,
    ( k1_xboole_0 != k7_relat_1(sK1,sK0)
    | ~ spl3_3 ),
    inference(subsumption_resolution,[],[f38,f73])).

fof(f38,plain,
    ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 != k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 != k7_relat_1(sK1,sK0) )
    & ( r1_xboole_0(k1_relat_1(sK1),sK0)
      | k1_xboole_0 = k7_relat_1(sK1,sK0) )
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f30])).

fof(f30,plain,
    ( ? [X0,X1] :
        ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 != k7_relat_1(X1,X0) )
        & ( r1_xboole_0(k1_relat_1(X1),X0)
          | k1_xboole_0 = k7_relat_1(X1,X0) )
        & v1_relat_1(X1) )
   => ( ( ~ r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 != k7_relat_1(sK1,sK0) )
      & ( r1_xboole_0(k1_relat_1(sK1),sK0)
        | k1_xboole_0 = k7_relat_1(sK1,sK0) )
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ? [X0,X1] :
      ( ( ~ r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 != k7_relat_1(X1,X0) )
      & ( r1_xboole_0(k1_relat_1(X1),X0)
        | k1_xboole_0 = k7_relat_1(X1,X0) )
      & v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0,X1] :
      ( ( k1_xboole_0 = k7_relat_1(X1,X0)
      <~> r1_xboole_0(k1_relat_1(X1),X0) )
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( k1_xboole_0 = k7_relat_1(X1,X0)
        <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k7_relat_1(X1,X0)
      <=> r1_xboole_0(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).

fof(f74,plain,
    ( spl3_2
    | spl3_3 ),
    inference(avatar_split_clause,[],[f37,f71,f67])).

fof(f37,plain,
    ( r1_xboole_0(k1_relat_1(sK1),sK0)
    | k1_xboole_0 = k7_relat_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f65,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f36,f62])).

fof(f36,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n015.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % WCLimit    : 600
% 0.15/0.34  % DateTime   : Tue Dec  1 13:52:23 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.42  % (7123)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.21/0.43  % (7121)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_10 on theBenchmark
% 0.21/0.44  % (7121)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f528,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f65,f74,f76,f80,f84,f89,f102,f110,f114,f126,f130,f141,f145,f175,f183,f187,f211,f259,f378,f414,f432,f472,f511,f527])).
% 0.21/0.44  fof(f527,plain,(
% 0.21/0.44    ~spl3_29 | ~spl3_47 | ~spl3_48 | ~spl3_49),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f526])).
% 0.21/0.44  fof(f526,plain,(
% 0.21/0.44    $false | (~spl3_29 | ~spl3_47 | ~spl3_48 | ~spl3_49)),
% 0.21/0.44    inference(subsumption_resolution,[],[f471,f512])).
% 0.21/0.44  fof(f512,plain,(
% 0.21/0.44    ~r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(sK1)) | (~spl3_29 | ~spl3_47 | ~spl3_49)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f210,f413,f510])).
% 0.21/0.44  fof(f510,plain,(
% 0.21/0.44    ( ! [X2] : (~r2_hidden(X2,k1_relat_1(sK1)) | ~r2_hidden(X2,sK0) | r2_hidden(X2,k1_xboole_0)) ) | ~spl3_49),
% 0.21/0.44    inference(avatar_component_clause,[],[f509])).
% 0.21/0.44  fof(f509,plain,(
% 0.21/0.44    spl3_49 <=> ! [X2] : (r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,sK0) | ~r2_hidden(X2,k1_relat_1(sK1)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.21/0.44  fof(f413,plain,(
% 0.21/0.44    r2_hidden(sK2(k1_relat_1(sK1),sK0),sK0) | ~spl3_47),
% 0.21/0.44    inference(avatar_component_clause,[],[f411])).
% 0.21/0.44  fof(f411,plain,(
% 0.21/0.44    spl3_47 <=> r2_hidden(sK2(k1_relat_1(sK1),sK0),sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.21/0.44  fof(f210,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | ~spl3_29),
% 0.21/0.44    inference(avatar_component_clause,[],[f209])).
% 0.21/0.44  fof(f209,plain,(
% 0.21/0.44    spl3_29 <=> ! [X0] : ~r2_hidden(X0,k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.44  fof(f471,plain,(
% 0.21/0.44    r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(sK1)) | ~spl3_48),
% 0.21/0.44    inference(avatar_component_clause,[],[f469])).
% 0.21/0.44  fof(f469,plain,(
% 0.21/0.44    spl3_48 <=> r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.21/0.44  fof(f511,plain,(
% 0.21/0.44    ~spl3_1 | spl3_49 | ~spl3_2 | ~spl3_6 | ~spl3_26),
% 0.21/0.44    inference(avatar_split_clause,[],[f395,f185,f86,f67,f509,f62])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    spl3_1 <=> v1_relat_1(sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    spl3_2 <=> k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.44  fof(f86,plain,(
% 0.21/0.44    spl3_6 <=> k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.44  fof(f185,plain,(
% 0.21/0.44    spl3_26 <=> ! [X1,X0,X2] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.44  fof(f395,plain,(
% 0.21/0.44    ( ! [X2] : (r2_hidden(X2,k1_xboole_0) | ~r2_hidden(X2,k1_relat_1(sK1)) | ~r2_hidden(X2,sK0) | ~v1_relat_1(sK1)) ) | (~spl3_2 | ~spl3_6 | ~spl3_26)),
% 0.21/0.44    inference(forward_demodulation,[],[f387,f88])).
% 0.21/0.44  fof(f88,plain,(
% 0.21/0.44    k1_xboole_0 = k1_relat_1(k1_xboole_0) | ~spl3_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f86])).
% 0.21/0.44  fof(f387,plain,(
% 0.21/0.44    ( ! [X2] : (r2_hidden(X2,k1_relat_1(k1_xboole_0)) | ~r2_hidden(X2,k1_relat_1(sK1)) | ~r2_hidden(X2,sK0) | ~v1_relat_1(sK1)) ) | (~spl3_2 | ~spl3_26)),
% 0.21/0.44    inference(superposition,[],[f186,f69])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    k1_xboole_0 = k7_relat_1(sK1,sK0) | ~spl3_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f67])).
% 0.21/0.44  fof(f186,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2)) ) | ~spl3_26),
% 0.21/0.44    inference(avatar_component_clause,[],[f185])).
% 0.21/0.44  fof(f472,plain,(
% 0.21/0.44    spl3_48 | spl3_3 | ~spl3_14),
% 0.21/0.44    inference(avatar_split_clause,[],[f383,f124,f71,f469])).
% 0.21/0.44  fof(f71,plain,(
% 0.21/0.44    spl3_3 <=> r1_xboole_0(k1_relat_1(sK1),sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.44  fof(f124,plain,(
% 0.21/0.44    spl3_14 <=> ! [X1,X0] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.44  fof(f383,plain,(
% 0.21/0.44    r2_hidden(sK2(k1_relat_1(sK1),sK0),k1_relat_1(sK1)) | (spl3_3 | ~spl3_14)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f72,f125])).
% 0.21/0.44  fof(f125,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) ) | ~spl3_14),
% 0.21/0.44    inference(avatar_component_clause,[],[f124])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    ~r1_xboole_0(k1_relat_1(sK1),sK0) | spl3_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f71])).
% 0.21/0.44  fof(f432,plain,(
% 0.21/0.44    spl3_2 | ~spl3_25 | ~spl3_46),
% 0.21/0.44    inference(avatar_contradiction_clause,[],[f431])).
% 0.21/0.44  fof(f431,plain,(
% 0.21/0.44    $false | (spl3_2 | ~spl3_25 | ~spl3_46)),
% 0.21/0.44    inference(subsumption_resolution,[],[f68,f427])).
% 0.21/0.44  fof(f427,plain,(
% 0.21/0.44    k1_xboole_0 = k7_relat_1(sK1,sK0) | (~spl3_25 | ~spl3_46)),
% 0.21/0.44    inference(superposition,[],[f377,f182])).
% 0.21/0.44  fof(f182,plain,(
% 0.21/0.44    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) ) | ~spl3_25),
% 0.21/0.44    inference(avatar_component_clause,[],[f181])).
% 0.21/0.44  fof(f181,plain,(
% 0.21/0.44    spl3_25 <=> ! [X0] : k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.44  fof(f377,plain,(
% 0.21/0.44    k1_xboole_0 = k5_relat_1(k6_relat_1(sK0),sK1) | ~spl3_46),
% 0.21/0.44    inference(avatar_component_clause,[],[f375])).
% 0.21/0.44  fof(f375,plain,(
% 0.21/0.44    spl3_46 <=> k1_xboole_0 = k5_relat_1(k6_relat_1(sK0),sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.21/0.44  fof(f68,plain,(
% 0.21/0.44    k1_xboole_0 != k7_relat_1(sK1,sK0) | spl3_2),
% 0.21/0.44    inference(avatar_component_clause,[],[f67])).
% 0.21/0.44  fof(f414,plain,(
% 0.21/0.44    spl3_47 | spl3_3 | ~spl3_15),
% 0.21/0.44    inference(avatar_split_clause,[],[f382,f128,f71,f411])).
% 0.21/0.44  fof(f128,plain,(
% 0.21/0.44    spl3_15 <=> ! [X1,X0] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.44  fof(f382,plain,(
% 0.21/0.44    r2_hidden(sK2(k1_relat_1(sK1),sK0),sK0) | (spl3_3 | ~spl3_15)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f72,f129])).
% 0.21/0.44  fof(f129,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) ) | ~spl3_15),
% 0.21/0.44    inference(avatar_component_clause,[],[f128])).
% 0.21/0.44  fof(f378,plain,(
% 0.21/0.44    spl3_46 | ~spl3_1 | ~spl3_4 | ~spl3_17 | ~spl3_37),
% 0.21/0.44    inference(avatar_split_clause,[],[f262,f257,f138,f78,f62,f375])).
% 0.21/0.44  fof(f78,plain,(
% 0.21/0.44    spl3_4 <=> ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.44  fof(f138,plain,(
% 0.21/0.44    spl3_17 <=> r1_xboole_0(sK0,k1_relat_1(sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.44  fof(f257,plain,(
% 0.21/0.44    spl3_37 <=> ! [X1,X2] : (~r1_xboole_0(X1,k1_relat_1(X2)) | k1_xboole_0 = k5_relat_1(k6_relat_1(X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(k6_relat_1(X1)))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.21/0.44  fof(f262,plain,(
% 0.21/0.44    k1_xboole_0 = k5_relat_1(k6_relat_1(sK0),sK1) | (~spl3_1 | ~spl3_4 | ~spl3_17 | ~spl3_37)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f64,f79,f140,f258])).
% 0.21/0.44  fof(f258,plain,(
% 0.21/0.44    ( ! [X2,X1] : (k1_xboole_0 = k5_relat_1(k6_relat_1(X1),X2) | ~r1_xboole_0(X1,k1_relat_1(X2)) | ~v1_relat_1(X2) | ~v1_relat_1(k6_relat_1(X1))) ) | ~spl3_37),
% 0.21/0.44    inference(avatar_component_clause,[],[f257])).
% 0.21/0.44  fof(f140,plain,(
% 0.21/0.44    r1_xboole_0(sK0,k1_relat_1(sK1)) | ~spl3_17),
% 0.21/0.44    inference(avatar_component_clause,[],[f138])).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) ) | ~spl3_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f78])).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    v1_relat_1(sK1) | ~spl3_1),
% 0.21/0.44    inference(avatar_component_clause,[],[f62])).
% 0.21/0.44  fof(f259,plain,(
% 0.21/0.44    spl3_37 | ~spl3_9 | ~spl3_23),
% 0.21/0.44    inference(avatar_split_clause,[],[f189,f173,f100,f257])).
% 0.21/0.44  fof(f100,plain,(
% 0.21/0.44    spl3_9 <=> ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.44  fof(f173,plain,(
% 0.21/0.44    spl3_23 <=> ! [X1,X0] : (k1_xboole_0 = k5_relat_1(X0,X1) | ~r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.44  fof(f189,plain,(
% 0.21/0.44    ( ! [X2,X1] : (~r1_xboole_0(X1,k1_relat_1(X2)) | k1_xboole_0 = k5_relat_1(k6_relat_1(X1),X2) | ~v1_relat_1(X2) | ~v1_relat_1(k6_relat_1(X1))) ) | (~spl3_9 | ~spl3_23)),
% 0.21/0.44    inference(superposition,[],[f174,f101])).
% 0.21/0.44  fof(f101,plain,(
% 0.21/0.44    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) ) | ~spl3_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f100])).
% 0.21/0.44  fof(f174,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1)) | k1_xboole_0 = k5_relat_1(X0,X1) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) ) | ~spl3_23),
% 0.21/0.44    inference(avatar_component_clause,[],[f173])).
% 0.21/0.44  fof(f211,plain,(
% 0.21/0.44    spl3_29 | ~spl3_5 | ~spl3_12),
% 0.21/0.44    inference(avatar_split_clause,[],[f131,f112,f82,f209])).
% 0.21/0.44  fof(f82,plain,(
% 0.21/0.44    spl3_5 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.44  fof(f112,plain,(
% 0.21/0.44    spl3_12 <=> ! [X1,X0] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.44  fof(f131,plain,(
% 0.21/0.44    ( ! [X0] : (~r2_hidden(X0,k1_xboole_0)) ) | (~spl3_5 | ~spl3_12)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f83,f113])).
% 0.21/0.44  fof(f113,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_xboole_0(k1_tarski(X0),X1) | ~r2_hidden(X0,X1)) ) | ~spl3_12),
% 0.21/0.44    inference(avatar_component_clause,[],[f112])).
% 0.21/0.44  fof(f83,plain,(
% 0.21/0.44    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl3_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f82])).
% 0.21/0.44  fof(f187,plain,(
% 0.21/0.44    spl3_26),
% 0.21/0.44    inference(avatar_split_clause,[],[f57,f185])).
% 0.21/0.44  fof(f57,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1) | ~v1_relat_1(X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f35])).
% 0.21/0.44  fof(f35,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | ~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1)) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.21/0.44    inference(flattening,[],[f34])).
% 0.21/0.44  fof(f34,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) | (~r2_hidden(X0,k1_relat_1(X2)) | ~r2_hidden(X0,X1))) & ((r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1)) | ~r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))))) | ~v1_relat_1(X2))),
% 0.21/0.44    inference(nnf_transformation,[],[f27])).
% 0.21/0.44  fof(f27,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))) | ~v1_relat_1(X2))),
% 0.21/0.44    inference(ennf_transformation,[],[f15])).
% 0.21/0.44  fof(f15,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) => (r2_hidden(X0,k1_relat_1(k7_relat_1(X2,X1))) <=> (r2_hidden(X0,k1_relat_1(X2)) & r2_hidden(X0,X1))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_relat_1)).
% 0.21/0.44  fof(f183,plain,(
% 0.21/0.44    spl3_25 | ~spl3_1 | ~spl3_18),
% 0.21/0.44    inference(avatar_split_clause,[],[f156,f143,f62,f181])).
% 0.21/0.44  fof(f143,plain,(
% 0.21/0.44    spl3_18 <=> ! [X1,X0] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.44  fof(f156,plain,(
% 0.21/0.44    ( ! [X0] : (k7_relat_1(sK1,X0) = k5_relat_1(k6_relat_1(X0),sK1)) ) | (~spl3_1 | ~spl3_18)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f64,f144])).
% 0.21/0.44  fof(f144,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) ) | ~spl3_18),
% 0.21/0.44    inference(avatar_component_clause,[],[f143])).
% 0.21/0.44  fof(f175,plain,(
% 0.21/0.44    spl3_23),
% 0.21/0.44    inference(avatar_split_clause,[],[f46,f173])).
% 0.21/0.44  fof(f46,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k1_xboole_0 = k5_relat_1(X0,X1) | ~r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : (k1_xboole_0 = k5_relat_1(X0,X1) | ~r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(flattening,[],[f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ! [X0] : (! [X1] : ((k1_xboole_0 = k5_relat_1(X0,X1) | ~r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1))) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f13])).
% 0.21/0.44  fof(f13,axiom,(
% 0.21/0.44    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => (r1_xboole_0(k2_relat_1(X0),k1_relat_1(X1)) => k1_xboole_0 = k5_relat_1(X0,X1))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_relat_1)).
% 0.21/0.44  fof(f145,plain,(
% 0.21/0.44    spl3_18),
% 0.21/0.44    inference(avatar_split_clause,[],[f51,f143])).
% 0.21/0.44  fof(f51,plain,(
% 0.21/0.44    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,axiom,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 0.21/0.44  fof(f141,plain,(
% 0.21/0.44    spl3_17 | ~spl3_3 | ~spl3_11),
% 0.21/0.44    inference(avatar_split_clause,[],[f115,f108,f71,f138])).
% 0.21/0.44  fof(f108,plain,(
% 0.21/0.44    spl3_11 <=> ! [X1,X0] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.44  fof(f115,plain,(
% 0.21/0.44    r1_xboole_0(sK0,k1_relat_1(sK1)) | (~spl3_3 | ~spl3_11)),
% 0.21/0.44    inference(unit_resulting_resolution,[],[f73,f109])).
% 0.21/0.44  fof(f109,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | r1_xboole_0(X1,X0)) ) | ~spl3_11),
% 0.21/0.44    inference(avatar_component_clause,[],[f108])).
% 0.21/0.44  fof(f73,plain,(
% 0.21/0.44    r1_xboole_0(k1_relat_1(sK1),sK0) | ~spl3_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f71])).
% 0.21/0.44  fof(f130,plain,(
% 0.21/0.44    spl3_15),
% 0.21/0.44    inference(avatar_split_clause,[],[f49,f128])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X1) | r1_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f33])).
% 0.21/0.44  fof(f33,plain,(
% 0.21/0.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & ((r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2])],[f23,f32])).
% 0.21/0.44  fof(f32,plain,(
% 0.21/0.44    ! [X1,X0] : (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) => (r2_hidden(sK2(X0,X1),X1) & r2_hidden(sK2(X0,X1),X0)))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ! [X0,X1] : ((~r1_xboole_0(X0,X1) | ! [X2] : (~r2_hidden(X2,X1) | ~r2_hidden(X2,X0))) & (? [X3] : (r2_hidden(X3,X1) & r2_hidden(X3,X0)) | r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(ennf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X3] : ~(r2_hidden(X3,X1) & r2_hidden(X3,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.44    inference(rectify,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1] : (~(r1_xboole_0(X0,X1) & ? [X2] : (r2_hidden(X2,X1) & r2_hidden(X2,X0))) & ~(! [X2] : ~(r2_hidden(X2,X1) & r2_hidden(X2,X0)) & ~r1_xboole_0(X0,X1)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).
% 0.21/0.44  fof(f126,plain,(
% 0.21/0.44    spl3_14),
% 0.21/0.44    inference(avatar_split_clause,[],[f48,f124])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r2_hidden(sK2(X0,X1),X0) | r1_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f33])).
% 0.21/0.44  fof(f114,plain,(
% 0.21/0.44    spl3_12),
% 0.21/0.44    inference(avatar_split_clause,[],[f53,f112])).
% 0.21/0.44  fof(f53,plain,(
% 0.21/0.44    ( ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f26])).
% 0.21/0.44  fof(f26,plain,(
% 0.21/0.44    ! [X0,X1] : (~r2_hidden(X0,X1) | ~r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f10])).
% 0.21/0.44  fof(f10,axiom,(
% 0.21/0.44    ! [X0,X1] : ~(r2_hidden(X0,X1) & r1_xboole_0(k1_tarski(X0),X1))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).
% 0.21/0.44  fof(f110,plain,(
% 0.21/0.44    spl3_11),
% 0.21/0.44    inference(avatar_split_clause,[],[f52,f108])).
% 0.21/0.44  fof(f52,plain,(
% 0.21/0.44    ( ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ! [X0,X1] : (r1_xboole_0(X1,X0) | ~r1_xboole_0(X0,X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0,X1] : (r1_xboole_0(X0,X1) => r1_xboole_0(X1,X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).
% 0.21/0.44  fof(f102,plain,(
% 0.21/0.44    spl3_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f45,f100])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,axiom,(
% 0.21/0.44    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.44  fof(f89,plain,(
% 0.21/0.44    spl3_6),
% 0.21/0.44    inference(avatar_split_clause,[],[f39,f86])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.44    inference(cnf_transformation,[],[f12])).
% 0.21/0.44  fof(f12,axiom,(
% 0.21/0.44    k1_xboole_0 = k2_relat_1(k1_xboole_0) & k1_xboole_0 = k1_relat_1(k1_xboole_0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).
% 0.21/0.44  fof(f84,plain,(
% 0.21/0.44    spl3_5),
% 0.21/0.44    inference(avatar_split_clause,[],[f42,f82])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.44  fof(f80,plain,(
% 0.21/0.44    spl3_4),
% 0.21/0.44    inference(avatar_split_clause,[],[f41,f78])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ( ! [X0] : (v1_relat_1(k6_relat_1(X0))) )),
% 0.21/0.44    inference(cnf_transformation,[],[f11])).
% 0.21/0.44  fof(f11,axiom,(
% 0.21/0.44    ! [X0] : v1_relat_1(k6_relat_1(X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_relat_1)).
% 0.21/0.44  fof(f76,plain,(
% 0.21/0.44    ~spl3_2 | ~spl3_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f75,f71,f67])).
% 0.21/0.44  fof(f75,plain,(
% 0.21/0.44    k1_xboole_0 != k7_relat_1(sK1,sK0) | ~spl3_3),
% 0.21/0.44    inference(subsumption_resolution,[],[f38,f73])).
% 0.21/0.44  fof(f38,plain,(
% 0.21/0.44    ~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f31])).
% 0.21/0.44  fof(f31,plain,(
% 0.21/0.44    (~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1)),
% 0.21/0.44    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f29,f30])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1)) => ((~r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 != k7_relat_1(sK1,sK0)) & (r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)) & v1_relat_1(sK1))),
% 0.21/0.44    introduced(choice_axiom,[])).
% 0.21/0.44  fof(f29,plain,(
% 0.21/0.44    ? [X0,X1] : ((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0)) & v1_relat_1(X1))),
% 0.21/0.44    inference(flattening,[],[f28])).
% 0.21/0.44  fof(f28,plain,(
% 0.21/0.44    ? [X0,X1] : (((~r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 != k7_relat_1(X1,X0)) & (r1_xboole_0(k1_relat_1(X1),X0) | k1_xboole_0 = k7_relat_1(X1,X0))) & v1_relat_1(X1))),
% 0.21/0.44    inference(nnf_transformation,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ? [X0,X1] : ((k1_xboole_0 = k7_relat_1(X1,X0) <~> r1_xboole_0(k1_relat_1(X1),X0)) & v1_relat_1(X1))),
% 0.21/0.44    inference(ennf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,negated_conjecture,(
% 0.21/0.44    ~! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.44    inference(negated_conjecture,[],[f17])).
% 0.21/0.44  fof(f17,conjecture,(
% 0.21/0.44    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k7_relat_1(X1,X0) <=> r1_xboole_0(k1_relat_1(X1),X0)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_relat_1)).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    spl3_2 | spl3_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f37,f71,f67])).
% 0.21/0.44  fof(f37,plain,(
% 0.21/0.44    r1_xboole_0(k1_relat_1(sK1),sK0) | k1_xboole_0 = k7_relat_1(sK1,sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f31])).
% 0.21/0.44  fof(f65,plain,(
% 0.21/0.44    spl3_1),
% 0.21/0.44    inference(avatar_split_clause,[],[f36,f62])).
% 0.21/0.44  fof(f36,plain,(
% 0.21/0.44    v1_relat_1(sK1)),
% 0.21/0.44    inference(cnf_transformation,[],[f31])).
% 0.21/0.44  % SZS output end Proof for theBenchmark
% 0.21/0.44  % (7121)------------------------------
% 0.21/0.44  % (7121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.44  % (7121)Termination reason: Refutation
% 0.21/0.44  
% 0.21/0.44  % (7121)Memory used [KB]: 6396
% 0.21/0.44  % (7121)Time elapsed: 0.038 s
% 0.21/0.44  % (7121)------------------------------
% 0.21/0.44  % (7121)------------------------------
% 0.21/0.45  % (7115)Success in time 0.086 s
%------------------------------------------------------------------------------
