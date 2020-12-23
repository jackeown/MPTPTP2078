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
% DateTime   : Thu Dec  3 13:01:57 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.81s
% Verified   : 
% Statistics : Number of formulae       :  221 ( 393 expanded)
%              Number of leaves         :   51 ( 166 expanded)
%              Depth                    :   13
%              Number of atoms          :  768 (1551 expanded)
%              Number of equality atoms :   78 ( 106 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1409,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f113,f118,f123,f128,f133,f138,f143,f148,f153,f160,f171,f209,f215,f228,f236,f573,f611,f656,f688,f717,f725,f788,f831,f941,f1212,f1387,f1408])).

fof(f1408,plain,
    ( spl4_1
    | ~ spl4_12
    | ~ spl4_54 ),
    inference(avatar_contradiction_clause,[],[f1407])).

fof(f1407,plain,
    ( $false
    | spl4_1
    | ~ spl4_12
    | ~ spl4_54 ),
    inference(subsumption_resolution,[],[f1404,f103])).

fof(f103,plain,
    ( ~ v2_funct_1(sK2)
    | spl4_1 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl4_1
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f1404,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_12
    | ~ spl4_54 ),
    inference(resolution,[],[f835,f174])).

fof(f174,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | v2_funct_1(X0) )
    | ~ spl4_12 ),
    inference(superposition,[],[f159,f82])).

fof(f82,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f159,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f157])).

fof(f157,plain,
    ( spl4_12
  <=> v2_funct_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f835,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_54 ),
    inference(avatar_component_clause,[],[f834])).

fof(f834,plain,
    ( spl4_54
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).

fof(f1387,plain,
    ( spl4_54
    | ~ spl4_11
    | ~ spl4_19
    | ~ spl4_90 ),
    inference(avatar_split_clause,[],[f1380,f1209,f212,f150,f834])).

fof(f150,plain,
    ( spl4_11
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f212,plain,
    ( spl4_19
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f1209,plain,
    ( spl4_90
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).

fof(f1380,plain,
    ( v1_xboole_0(sK2)
    | ~ spl4_11
    | ~ spl4_19
    | ~ spl4_90 ),
    inference(subsumption_resolution,[],[f1379,f214])).

fof(f214,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f212])).

fof(f1379,plain,
    ( ~ v1_relat_1(sK2)
    | v1_xboole_0(sK2)
    | ~ spl4_11
    | ~ spl4_90 ),
    inference(subsumption_resolution,[],[f1370,f152])).

fof(f152,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f150])).

fof(f1370,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1(sK2)
    | v1_xboole_0(sK2)
    | ~ spl4_90 ),
    inference(superposition,[],[f91,f1211])).

fof(f1211,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_90 ),
    inference(avatar_component_clause,[],[f1209])).

fof(f91,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_relat_1(X0)
        & ~ v1_xboole_0(X0) )
     => ~ v1_xboole_0(k1_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

fof(f1212,plain,
    ( spl4_90
    | ~ spl4_41
    | ~ spl4_49 ),
    inference(avatar_split_clause,[],[f1207,f764,f675,f1209])).

fof(f675,plain,
    ( spl4_41
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f764,plain,
    ( spl4_49
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).

fof(f1207,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl4_41
    | ~ spl4_49 ),
    inference(forward_demodulation,[],[f766,f677])).

fof(f677,plain,
    ( k1_xboole_0 = sK0
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f675])).

fof(f766,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_49 ),
    inference(avatar_component_clause,[],[f764])).

fof(f941,plain,
    ( spl4_2
    | ~ spl4_18
    | ~ spl4_22
    | ~ spl4_46 ),
    inference(avatar_split_clause,[],[f940,f743,f233,f206,f105])).

fof(f105,plain,
    ( spl4_2
  <=> v2_funct_2(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f206,plain,
    ( spl4_18
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f233,plain,
    ( spl4_22
  <=> v5_relat_1(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).

fof(f743,plain,
    ( spl4_46
  <=> sK0 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f940,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ spl4_18
    | ~ spl4_22
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f921,f208])).

fof(f208,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f206])).

fof(f921,plain,
    ( v2_funct_2(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_22
    | ~ spl4_46 ),
    inference(subsumption_resolution,[],[f910,f235])).

fof(f235,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl4_22 ),
    inference(avatar_component_clause,[],[f233])).

fof(f910,plain,
    ( ~ v5_relat_1(sK3,sK0)
    | v2_funct_2(sK3,sK0)
    | ~ v1_relat_1(sK3)
    | ~ spl4_46 ),
    inference(superposition,[],[f94,f745])).

fof(f745,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_46 ),
    inference(avatar_component_clause,[],[f743])).

fof(f94,plain,(
    ! [X1] :
      ( ~ v5_relat_1(X1,k2_relat_1(X1))
      | v2_funct_2(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_funct_2(X1,X0)
      | k2_relat_1(X1) != X0
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( ( v2_funct_2(X1,X0)
          | k2_relat_1(X1) != X0 )
        & ( k2_relat_1(X1) = X0
          | ~ v2_funct_2(X1,X0) ) )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f831,plain,
    ( spl4_49
    | ~ spl4_19
    | ~ spl4_21
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f830,f722,f225,f212,f764])).

fof(f225,plain,
    ( spl4_21
  <=> v4_relat_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f722,plain,
    ( spl4_43
  <=> r1_tarski(sK0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f830,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_19
    | ~ spl4_21
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f829,f227])).

fof(f227,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f225])).

fof(f829,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | ~ spl4_19
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f826,f214])).

fof(f826,plain,
    ( ~ v1_relat_1(sK2)
    | sK0 = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,sK0)
    | ~ spl4_43 ),
    inference(resolution,[],[f724,f255])).

fof(f255,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k1_relat_1(X0) = X1
      | ~ v4_relat_1(X0,X1) ) ),
    inference(resolution,[],[f89,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f89,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v4_relat_1(X1,X0)
          | ~ r1_tarski(k1_relat_1(X1),X0) )
        & ( r1_tarski(k1_relat_1(X1),X0)
          | ~ v4_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f724,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f722])).

fof(f788,plain,
    ( spl4_46
    | ~ spl4_18
    | ~ spl4_22
    | ~ spl4_42 ),
    inference(avatar_split_clause,[],[f787,f714,f233,f206,f743])).

fof(f714,plain,
    ( spl4_42
  <=> r1_tarski(sK0,k2_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f787,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ spl4_18
    | ~ spl4_22
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f786,f235])).

fof(f786,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ v5_relat_1(sK3,sK0)
    | ~ spl4_18
    | ~ spl4_42 ),
    inference(subsumption_resolution,[],[f782,f208])).

fof(f782,plain,
    ( ~ v1_relat_1(sK3)
    | sK0 = k2_relat_1(sK3)
    | ~ v5_relat_1(sK3,sK0)
    | ~ spl4_42 ),
    inference(resolution,[],[f716,f243])).

fof(f243,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,k2_relat_1(X0))
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = X1
      | ~ v5_relat_1(X0,X1) ) ),
    inference(resolution,[],[f86,f81])).

fof(f86,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(X1),X0)
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ( ( v5_relat_1(X1,X0)
          | ~ r1_tarski(k2_relat_1(X1),X0) )
        & ( r1_tarski(k2_relat_1(X1),X0)
          | ~ v5_relat_1(X1,X0) ) )
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v5_relat_1(X1,X0)
      <=> r1_tarski(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).

fof(f716,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3))
    | ~ spl4_42 ),
    inference(avatar_component_clause,[],[f714])).

fof(f725,plain,
    ( spl4_43
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f720,f579,f212,f206,f722])).

fof(f579,plain,
    ( spl4_37
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f720,plain,
    ( r1_tarski(sK0,k1_relat_1(sK2))
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f719,f83])).

fof(f83,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f719,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(sK0)),k1_relat_1(sK2))
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f718,f214])).

fof(f718,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(sK0)),k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_18
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f702,f208])).

fof(f702,plain,
    ( r1_tarski(k1_relat_1(k6_relat_1(sK0)),k1_relat_1(sK2))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl4_37 ),
    inference(superposition,[],[f92,f581])).

fof(f581,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f579])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).

fof(f717,plain,
    ( spl4_42
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_37 ),
    inference(avatar_split_clause,[],[f712,f579,f212,f206,f714])).

fof(f712,plain,
    ( r1_tarski(sK0,k2_relat_1(sK3))
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_37 ),
    inference(forward_demodulation,[],[f711,f84])).

fof(f84,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f711,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK0)),k2_relat_1(sK3))
    | ~ spl4_18
    | ~ spl4_19
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f710,f214])).

fof(f710,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK0)),k2_relat_1(sK3))
    | ~ v1_relat_1(sK2)
    | ~ spl4_18
    | ~ spl4_37 ),
    inference(subsumption_resolution,[],[f701,f208])).

fof(f701,plain,
    ( r1_tarski(k2_relat_1(k6_relat_1(sK0)),k2_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | ~ spl4_37 ),
    inference(superposition,[],[f88,f581])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f688,plain,
    ( spl4_1
    | spl4_41
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f687,f570,f140,f135,f130,f125,f120,f115,f675,f101])).

fof(f115,plain,
    ( spl4_4
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f120,plain,
    ( spl4_5
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f125,plain,
    ( spl4_6
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f130,plain,
    ( spl4_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f135,plain,
    ( spl4_8
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f140,plain,
    ( spl4_9
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f570,plain,
    ( spl4_35
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).

fof(f687,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f686,f142])).

fof(f142,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f140])).

fof(f686,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f685,f137])).

fof(f137,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f135])).

fof(f685,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f684,f132])).

fof(f132,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f130])).

fof(f684,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_6
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f683,f127])).

fof(f127,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f125])).

fof(f683,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_5
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f682,f122])).

fof(f122,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f120])).

fof(f682,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f666,f117])).

fof(f117,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f115])).

fof(f666,plain,
    ( k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f646,f67])).

fof(f67,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f646,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_35 ),
    inference(superposition,[],[f64,f572])).

fof(f572,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ spl4_35 ),
    inference(avatar_component_clause,[],[f570])).

fof(f64,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k1_xboole_0 = X2
      | v2_funct_1(X3)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( v2_funct_1(X3)
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
           => ( v2_funct_1(X3)
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).

fof(f656,plain,
    ( spl4_37
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_35 ),
    inference(avatar_split_clause,[],[f655,f570,f140,f130,f125,f115,f579])).

fof(f655,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f654,f142])).

fof(f654,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f653,f132])).

fof(f653,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f652,f127])).

fof(f652,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_35 ),
    inference(subsumption_resolution,[],[f644,f117])).

fof(f644,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_35 ),
    inference(superposition,[],[f73,f572])).

fof(f73,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f611,plain,
    ( ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_9
    | spl4_34 ),
    inference(avatar_contradiction_clause,[],[f610])).

fof(f610,plain,
    ( $false
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_9
    | spl4_34 ),
    inference(subsumption_resolution,[],[f609,f142])).

fof(f609,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_7
    | spl4_34 ),
    inference(subsumption_resolution,[],[f608,f132])).

fof(f608,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | ~ spl4_6
    | spl4_34 ),
    inference(subsumption_resolution,[],[f607,f127])).

fof(f607,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_4
    | spl4_34 ),
    inference(subsumption_resolution,[],[f604,f117])).

fof(f604,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_34 ),
    inference(resolution,[],[f568,f72])).

fof(f72,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f568,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_34 ),
    inference(avatar_component_clause,[],[f566])).

fof(f566,plain,
    ( spl4_34
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).

fof(f573,plain,
    ( ~ spl4_34
    | spl4_35
    | ~ spl4_14 ),
    inference(avatar_split_clause,[],[f561,f168,f570,f566])).

fof(f168,plain,
    ( spl4_14
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f561,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_14 ),
    inference(resolution,[],[f327,f170])).

fof(f170,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f168])).

fof(f327,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f68,f77])).

fof(f77,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f236,plain,
    ( spl4_22
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f229,f115,f233])).

fof(f229,plain,
    ( v5_relat_1(sK3,sK0)
    | ~ spl4_4 ),
    inference(resolution,[],[f75,f117])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f228,plain,
    ( spl4_21
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f217,f130,f225])).

fof(f217,plain,
    ( v4_relat_1(sK2,sK0)
    | ~ spl4_7 ),
    inference(resolution,[],[f74,f132])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f215,plain,
    ( spl4_19
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f210,f130,f212])).

fof(f210,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f202,f78])).

fof(f78,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f202,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_7 ),
    inference(resolution,[],[f76,f132])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f209,plain,
    ( spl4_18
    | ~ spl4_4 ),
    inference(avatar_split_clause,[],[f204,f115,f206])).

fof(f204,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_4 ),
    inference(subsumption_resolution,[],[f201,f78])).

fof(f201,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl4_4 ),
    inference(resolution,[],[f76,f117])).

fof(f171,plain,
    ( spl4_14
    | ~ spl4_3 ),
    inference(avatar_split_clause,[],[f166,f110,f168])).

fof(f110,plain,
    ( spl4_3
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f166,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_3 ),
    inference(backward_demodulation,[],[f112,f70])).

fof(f70,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f112,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f160,plain,
    ( spl4_12
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f154,f145,f157])).

fof(f145,plain,
    ( spl4_10
  <=> k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f154,plain,
    ( v2_funct_1(k1_xboole_0)
    | ~ spl4_10 ),
    inference(superposition,[],[f67,f147])).

fof(f147,plain,
    ( k1_xboole_0 = k6_relat_1(k1_xboole_0)
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f145])).

fof(f153,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f93,f150])).

fof(f93,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f148,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f85,f145])).

fof(f85,plain,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    k1_xboole_0 = k6_relat_1(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).

fof(f143,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f54,f140])).

fof(f54,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,
    ( ( ~ v2_funct_2(sK3,sK0)
      | ~ v2_funct_1(sK2) )
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f46,f45])).

fof(f45,plain,
    ( ? [X0,X1,X2] :
        ( ? [X3] :
            ( ( ~ v2_funct_2(X3,X0)
              | ~ v2_funct_1(X2) )
            & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
            & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( ( ~ v2_funct_2(X3,sK0)
            | ~ v2_funct_1(sK2) )
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f46,plain,
    ( ? [X3] :
        ( ( ~ v2_funct_2(X3,sK0)
          | ~ v2_funct_1(sK2) )
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( ( ~ v2_funct_2(sK3,sK0)
        | ~ v2_funct_1(sK2) )
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( ( ~ v2_funct_2(X3,X0)
            | ~ v2_funct_1(X2) )
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
             => ( v2_funct_2(X3,X0)
                & v2_funct_1(X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
           => ( v2_funct_2(X3,X0)
              & v2_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).

fof(f138,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f55,f135])).

fof(f55,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f47])).

fof(f133,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f56,f130])).

fof(f56,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f47])).

fof(f128,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f57,f125])).

fof(f57,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f47])).

fof(f123,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f58,f120])).

fof(f58,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f47])).

fof(f118,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f59,f115])).

fof(f59,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f47])).

fof(f113,plain,(
    spl4_3 ),
    inference(avatar_split_clause,[],[f60,f110])).

fof(f60,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f47])).

fof(f108,plain,
    ( ~ spl4_1
    | ~ spl4_2 ),
    inference(avatar_split_clause,[],[f61,f105,f101])).

fof(f61,plain,
    ( ~ v2_funct_2(sK3,sK0)
    | ~ v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n022.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:27:11 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.51  % (20945)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.51  % (20933)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.52  % (20961)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (20936)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (20932)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.52  % (20953)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.54  % (20954)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (20946)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (20943)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.54  % (20934)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.54  % (20935)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (20937)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.55  % (20939)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.55  % (20938)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (20959)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.55  % (20955)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.55  % (20944)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.55  % (20957)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.55  % (20958)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.55  % (20951)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (20948)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.56  % (20949)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (20948)Refutation not found, incomplete strategy% (20948)------------------------------
% 0.22/0.56  % (20948)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (20948)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (20948)Memory used [KB]: 10746
% 0.22/0.56  % (20948)Time elapsed: 0.144 s
% 0.22/0.56  % (20948)------------------------------
% 0.22/0.56  % (20948)------------------------------
% 0.22/0.56  % (20960)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.56  % (20956)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.56  % (20950)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  % (20960)Refutation not found, incomplete strategy% (20960)------------------------------
% 0.22/0.56  % (20960)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.56  % (20960)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.56  
% 0.22/0.56  % (20960)Memory used [KB]: 10874
% 0.22/0.56  % (20960)Time elapsed: 0.150 s
% 0.22/0.56  % (20960)------------------------------
% 0.22/0.56  % (20960)------------------------------
% 0.22/0.56  % (20941)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.56  % (20952)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.56  % (20942)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.56  % (20947)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.57  % (20942)Refutation not found, incomplete strategy% (20942)------------------------------
% 0.22/0.57  % (20942)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.57  % (20942)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.57  
% 0.22/0.57  % (20942)Memory used [KB]: 10874
% 0.22/0.57  % (20942)Time elapsed: 0.160 s
% 0.22/0.57  % (20942)------------------------------
% 0.22/0.57  % (20942)------------------------------
% 0.22/0.57  % (20940)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.60  % (20953)Refutation found. Thanks to Tanya!
% 0.22/0.60  % SZS status Theorem for theBenchmark
% 1.81/0.61  % SZS output start Proof for theBenchmark
% 1.81/0.61  fof(f1409,plain,(
% 1.81/0.61    $false),
% 1.81/0.61    inference(avatar_sat_refutation,[],[f108,f113,f118,f123,f128,f133,f138,f143,f148,f153,f160,f171,f209,f215,f228,f236,f573,f611,f656,f688,f717,f725,f788,f831,f941,f1212,f1387,f1408])).
% 1.81/0.61  fof(f1408,plain,(
% 1.81/0.61    spl4_1 | ~spl4_12 | ~spl4_54),
% 1.81/0.61    inference(avatar_contradiction_clause,[],[f1407])).
% 1.81/0.61  fof(f1407,plain,(
% 1.81/0.61    $false | (spl4_1 | ~spl4_12 | ~spl4_54)),
% 1.81/0.61    inference(subsumption_resolution,[],[f1404,f103])).
% 1.81/0.61  fof(f103,plain,(
% 1.81/0.61    ~v2_funct_1(sK2) | spl4_1),
% 1.81/0.61    inference(avatar_component_clause,[],[f101])).
% 1.81/0.61  fof(f101,plain,(
% 1.81/0.61    spl4_1 <=> v2_funct_1(sK2)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 1.81/0.61  fof(f1404,plain,(
% 1.81/0.61    v2_funct_1(sK2) | (~spl4_12 | ~spl4_54)),
% 1.81/0.61    inference(resolution,[],[f835,f174])).
% 1.81/0.61  fof(f174,plain,(
% 1.81/0.61    ( ! [X0] : (~v1_xboole_0(X0) | v2_funct_1(X0)) ) | ~spl4_12),
% 1.81/0.61    inference(superposition,[],[f159,f82])).
% 1.81/0.61  fof(f82,plain,(
% 1.81/0.61    ( ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f38])).
% 1.81/0.61  fof(f38,plain,(
% 1.81/0.61    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 1.81/0.61    inference(ennf_transformation,[],[f2])).
% 1.81/0.61  fof(f2,axiom,(
% 1.81/0.61    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 1.81/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 1.81/0.61  fof(f159,plain,(
% 1.81/0.61    v2_funct_1(k1_xboole_0) | ~spl4_12),
% 1.81/0.61    inference(avatar_component_clause,[],[f157])).
% 1.81/0.61  fof(f157,plain,(
% 1.81/0.61    spl4_12 <=> v2_funct_1(k1_xboole_0)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 1.81/0.61  fof(f835,plain,(
% 1.81/0.61    v1_xboole_0(sK2) | ~spl4_54),
% 1.81/0.61    inference(avatar_component_clause,[],[f834])).
% 1.81/0.61  fof(f834,plain,(
% 1.81/0.61    spl4_54 <=> v1_xboole_0(sK2)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_54])])).
% 1.81/0.61  fof(f1387,plain,(
% 1.81/0.61    spl4_54 | ~spl4_11 | ~spl4_19 | ~spl4_90),
% 1.81/0.61    inference(avatar_split_clause,[],[f1380,f1209,f212,f150,f834])).
% 1.81/0.61  fof(f150,plain,(
% 1.81/0.61    spl4_11 <=> v1_xboole_0(k1_xboole_0)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 1.81/0.61  fof(f212,plain,(
% 1.81/0.61    spl4_19 <=> v1_relat_1(sK2)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.81/0.61  fof(f1209,plain,(
% 1.81/0.61    spl4_90 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_90])])).
% 1.81/0.61  fof(f1380,plain,(
% 1.81/0.61    v1_xboole_0(sK2) | (~spl4_11 | ~spl4_19 | ~spl4_90)),
% 1.81/0.61    inference(subsumption_resolution,[],[f1379,f214])).
% 1.81/0.61  fof(f214,plain,(
% 1.81/0.61    v1_relat_1(sK2) | ~spl4_19),
% 1.81/0.61    inference(avatar_component_clause,[],[f212])).
% 1.81/0.61  fof(f1379,plain,(
% 1.81/0.61    ~v1_relat_1(sK2) | v1_xboole_0(sK2) | (~spl4_11 | ~spl4_90)),
% 1.81/0.61    inference(subsumption_resolution,[],[f1370,f152])).
% 1.81/0.61  fof(f152,plain,(
% 1.81/0.61    v1_xboole_0(k1_xboole_0) | ~spl4_11),
% 1.81/0.61    inference(avatar_component_clause,[],[f150])).
% 1.81/0.61  fof(f1370,plain,(
% 1.81/0.61    ~v1_xboole_0(k1_xboole_0) | ~v1_relat_1(sK2) | v1_xboole_0(sK2) | ~spl4_90),
% 1.81/0.61    inference(superposition,[],[f91,f1211])).
% 1.81/0.61  fof(f1211,plain,(
% 1.81/0.61    k1_xboole_0 = k1_relat_1(sK2) | ~spl4_90),
% 1.81/0.61    inference(avatar_component_clause,[],[f1209])).
% 1.81/0.61  fof(f91,plain,(
% 1.81/0.61    ( ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0)) )),
% 1.81/0.61    inference(cnf_transformation,[],[f43])).
% 1.81/0.61  fof(f43,plain,(
% 1.81/0.61    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | ~v1_relat_1(X0) | v1_xboole_0(X0))),
% 1.81/0.61    inference(flattening,[],[f42])).
% 1.81/0.61  fof(f42,plain,(
% 1.81/0.61    ! [X0] : (~v1_xboole_0(k1_relat_1(X0)) | (~v1_relat_1(X0) | v1_xboole_0(X0)))),
% 1.81/0.61    inference(ennf_transformation,[],[f8])).
% 1.81/0.61  fof(f8,axiom,(
% 1.81/0.61    ! [X0] : ((v1_relat_1(X0) & ~v1_xboole_0(X0)) => ~v1_xboole_0(k1_relat_1(X0)))),
% 1.81/0.61    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).
% 1.81/0.61  fof(f1212,plain,(
% 1.81/0.61    spl4_90 | ~spl4_41 | ~spl4_49),
% 1.81/0.61    inference(avatar_split_clause,[],[f1207,f764,f675,f1209])).
% 1.81/0.61  fof(f675,plain,(
% 1.81/0.61    spl4_41 <=> k1_xboole_0 = sK0),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 1.81/0.61  fof(f764,plain,(
% 1.81/0.61    spl4_49 <=> sK0 = k1_relat_1(sK2)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_49])])).
% 1.81/0.61  fof(f1207,plain,(
% 1.81/0.61    k1_xboole_0 = k1_relat_1(sK2) | (~spl4_41 | ~spl4_49)),
% 1.81/0.61    inference(forward_demodulation,[],[f766,f677])).
% 1.81/0.61  fof(f677,plain,(
% 1.81/0.61    k1_xboole_0 = sK0 | ~spl4_41),
% 1.81/0.61    inference(avatar_component_clause,[],[f675])).
% 1.81/0.61  fof(f766,plain,(
% 1.81/0.61    sK0 = k1_relat_1(sK2) | ~spl4_49),
% 1.81/0.61    inference(avatar_component_clause,[],[f764])).
% 1.81/0.61  fof(f941,plain,(
% 1.81/0.61    spl4_2 | ~spl4_18 | ~spl4_22 | ~spl4_46),
% 1.81/0.61    inference(avatar_split_clause,[],[f940,f743,f233,f206,f105])).
% 1.81/0.61  fof(f105,plain,(
% 1.81/0.61    spl4_2 <=> v2_funct_2(sK3,sK0)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 1.81/0.61  fof(f206,plain,(
% 1.81/0.61    spl4_18 <=> v1_relat_1(sK3)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 1.81/0.61  fof(f233,plain,(
% 1.81/0.61    spl4_22 <=> v5_relat_1(sK3,sK0)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_22])])).
% 1.81/0.61  fof(f743,plain,(
% 1.81/0.61    spl4_46 <=> sK0 = k2_relat_1(sK3)),
% 1.81/0.61    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 1.81/0.61  fof(f940,plain,(
% 1.81/0.61    v2_funct_2(sK3,sK0) | (~spl4_18 | ~spl4_22 | ~spl4_46)),
% 1.81/0.61    inference(subsumption_resolution,[],[f921,f208])).
% 1.81/0.61  fof(f208,plain,(
% 1.81/0.61    v1_relat_1(sK3) | ~spl4_18),
% 1.81/0.61    inference(avatar_component_clause,[],[f206])).
% 1.81/0.61  fof(f921,plain,(
% 1.81/0.61    v2_funct_2(sK3,sK0) | ~v1_relat_1(sK3) | (~spl4_22 | ~spl4_46)),
% 1.81/0.61    inference(subsumption_resolution,[],[f910,f235])).
% 1.81/0.61  fof(f235,plain,(
% 1.81/0.61    v5_relat_1(sK3,sK0) | ~spl4_22),
% 1.81/0.61    inference(avatar_component_clause,[],[f233])).
% 1.81/0.61  fof(f910,plain,(
% 1.81/0.61    ~v5_relat_1(sK3,sK0) | v2_funct_2(sK3,sK0) | ~v1_relat_1(sK3) | ~spl4_46),
% 1.81/0.61    inference(superposition,[],[f94,f745])).
% 1.81/0.62  fof(f745,plain,(
% 1.81/0.62    sK0 = k2_relat_1(sK3) | ~spl4_46),
% 1.81/0.62    inference(avatar_component_clause,[],[f743])).
% 1.81/0.62  fof(f94,plain,(
% 1.81/0.62    ( ! [X1] : (~v5_relat_1(X1,k2_relat_1(X1)) | v2_funct_2(X1,k2_relat_1(X1)) | ~v1_relat_1(X1)) )),
% 1.81/0.62    inference(equality_resolution,[],[f63])).
% 1.81/0.62  fof(f63,plain,(
% 1.81/0.62    ( ! [X0,X1] : (v2_funct_2(X1,X0) | k2_relat_1(X1) != X0 | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f48])).
% 1.81/0.62  fof(f48,plain,(
% 1.81/0.62    ! [X0,X1] : (((v2_funct_2(X1,X0) | k2_relat_1(X1) != X0) & (k2_relat_1(X1) = X0 | ~v2_funct_2(X1,X0))) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.81/0.62    inference(nnf_transformation,[],[f27])).
% 1.81/0.62  fof(f27,plain,(
% 1.81/0.62    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.81/0.62    inference(flattening,[],[f26])).
% 1.81/0.62  fof(f26,plain,(
% 1.81/0.62    ! [X0,X1] : ((v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0) | (~v5_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.81/0.62    inference(ennf_transformation,[],[f17])).
% 1.81/0.62  fof(f17,axiom,(
% 1.81/0.62    ! [X0,X1] : ((v5_relat_1(X1,X0) & v1_relat_1(X1)) => (v2_funct_2(X1,X0) <=> k2_relat_1(X1) = X0))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).
% 1.81/0.62  fof(f831,plain,(
% 1.81/0.62    spl4_49 | ~spl4_19 | ~spl4_21 | ~spl4_43),
% 1.81/0.62    inference(avatar_split_clause,[],[f830,f722,f225,f212,f764])).
% 1.81/0.62  fof(f225,plain,(
% 1.81/0.62    spl4_21 <=> v4_relat_1(sK2,sK0)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 1.81/0.62  fof(f722,plain,(
% 1.81/0.62    spl4_43 <=> r1_tarski(sK0,k1_relat_1(sK2))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 1.81/0.62  fof(f830,plain,(
% 1.81/0.62    sK0 = k1_relat_1(sK2) | (~spl4_19 | ~spl4_21 | ~spl4_43)),
% 1.81/0.62    inference(subsumption_resolution,[],[f829,f227])).
% 1.81/0.62  fof(f227,plain,(
% 1.81/0.62    v4_relat_1(sK2,sK0) | ~spl4_21),
% 1.81/0.62    inference(avatar_component_clause,[],[f225])).
% 1.81/0.62  fof(f829,plain,(
% 1.81/0.62    sK0 = k1_relat_1(sK2) | ~v4_relat_1(sK2,sK0) | (~spl4_19 | ~spl4_43)),
% 1.81/0.62    inference(subsumption_resolution,[],[f826,f214])).
% 1.81/0.62  fof(f826,plain,(
% 1.81/0.62    ~v1_relat_1(sK2) | sK0 = k1_relat_1(sK2) | ~v4_relat_1(sK2,sK0) | ~spl4_43),
% 1.81/0.62    inference(resolution,[],[f724,f255])).
% 1.81/0.62  fof(f255,plain,(
% 1.81/0.62    ( ! [X0,X1] : (~r1_tarski(X1,k1_relat_1(X0)) | ~v1_relat_1(X0) | k1_relat_1(X0) = X1 | ~v4_relat_1(X0,X1)) )),
% 1.81/0.62    inference(resolution,[],[f89,f81])).
% 1.81/0.62  fof(f81,plain,(
% 1.81/0.62    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f51])).
% 1.81/0.62  fof(f51,plain,(
% 1.81/0.62    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.81/0.62    inference(flattening,[],[f50])).
% 1.81/0.62  fof(f50,plain,(
% 1.81/0.62    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 1.81/0.62    inference(nnf_transformation,[],[f3])).
% 1.81/0.62  fof(f3,axiom,(
% 1.81/0.62    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.81/0.62  fof(f89,plain,(
% 1.81/0.62    ( ! [X0,X1] : (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f53])).
% 1.81/0.62  fof(f53,plain,(
% 1.81/0.62    ! [X0,X1] : (((v4_relat_1(X1,X0) | ~r1_tarski(k1_relat_1(X1),X0)) & (r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.81/0.62    inference(nnf_transformation,[],[f41])).
% 1.81/0.62  fof(f41,plain,(
% 1.81/0.62    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.81/0.62    inference(ennf_transformation,[],[f5])).
% 1.81/0.62  fof(f5,axiom,(
% 1.81/0.62    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.81/0.62  fof(f724,plain,(
% 1.81/0.62    r1_tarski(sK0,k1_relat_1(sK2)) | ~spl4_43),
% 1.81/0.62    inference(avatar_component_clause,[],[f722])).
% 1.81/0.62  fof(f788,plain,(
% 1.81/0.62    spl4_46 | ~spl4_18 | ~spl4_22 | ~spl4_42),
% 1.81/0.62    inference(avatar_split_clause,[],[f787,f714,f233,f206,f743])).
% 1.81/0.62  fof(f714,plain,(
% 1.81/0.62    spl4_42 <=> r1_tarski(sK0,k2_relat_1(sK3))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 1.81/0.62  fof(f787,plain,(
% 1.81/0.62    sK0 = k2_relat_1(sK3) | (~spl4_18 | ~spl4_22 | ~spl4_42)),
% 1.81/0.62    inference(subsumption_resolution,[],[f786,f235])).
% 1.81/0.62  fof(f786,plain,(
% 1.81/0.62    sK0 = k2_relat_1(sK3) | ~v5_relat_1(sK3,sK0) | (~spl4_18 | ~spl4_42)),
% 1.81/0.62    inference(subsumption_resolution,[],[f782,f208])).
% 1.81/0.62  fof(f782,plain,(
% 1.81/0.62    ~v1_relat_1(sK3) | sK0 = k2_relat_1(sK3) | ~v5_relat_1(sK3,sK0) | ~spl4_42),
% 1.81/0.62    inference(resolution,[],[f716,f243])).
% 1.81/0.62  fof(f243,plain,(
% 1.81/0.62    ( ! [X0,X1] : (~r1_tarski(X1,k2_relat_1(X0)) | ~v1_relat_1(X0) | k2_relat_1(X0) = X1 | ~v5_relat_1(X0,X1)) )),
% 1.81/0.62    inference(resolution,[],[f86,f81])).
% 1.81/0.62  fof(f86,plain,(
% 1.81/0.62    ( ! [X0,X1] : (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f52])).
% 1.81/0.62  fof(f52,plain,(
% 1.81/0.62    ! [X0,X1] : (((v5_relat_1(X1,X0) | ~r1_tarski(k2_relat_1(X1),X0)) & (r1_tarski(k2_relat_1(X1),X0) | ~v5_relat_1(X1,X0))) | ~v1_relat_1(X1))),
% 1.81/0.62    inference(nnf_transformation,[],[f39])).
% 1.81/0.62  fof(f39,plain,(
% 1.81/0.62    ! [X0,X1] : ((v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.81/0.62    inference(ennf_transformation,[],[f6])).
% 1.81/0.62  fof(f6,axiom,(
% 1.81/0.62    ! [X0,X1] : (v1_relat_1(X1) => (v5_relat_1(X1,X0) <=> r1_tarski(k2_relat_1(X1),X0)))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d19_relat_1)).
% 1.81/0.62  fof(f716,plain,(
% 1.81/0.62    r1_tarski(sK0,k2_relat_1(sK3)) | ~spl4_42),
% 1.81/0.62    inference(avatar_component_clause,[],[f714])).
% 1.81/0.62  fof(f725,plain,(
% 1.81/0.62    spl4_43 | ~spl4_18 | ~spl4_19 | ~spl4_37),
% 1.81/0.62    inference(avatar_split_clause,[],[f720,f579,f212,f206,f722])).
% 1.81/0.62  fof(f579,plain,(
% 1.81/0.62    spl4_37 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 1.81/0.62  fof(f720,plain,(
% 1.81/0.62    r1_tarski(sK0,k1_relat_1(sK2)) | (~spl4_18 | ~spl4_19 | ~spl4_37)),
% 1.81/0.62    inference(forward_demodulation,[],[f719,f83])).
% 1.81/0.62  fof(f83,plain,(
% 1.81/0.62    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.81/0.62    inference(cnf_transformation,[],[f11])).
% 1.81/0.62  fof(f11,axiom,(
% 1.81/0.62    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.81/0.62  fof(f719,plain,(
% 1.81/0.62    r1_tarski(k1_relat_1(k6_relat_1(sK0)),k1_relat_1(sK2)) | (~spl4_18 | ~spl4_19 | ~spl4_37)),
% 1.81/0.62    inference(subsumption_resolution,[],[f718,f214])).
% 1.81/0.62  fof(f718,plain,(
% 1.81/0.62    r1_tarski(k1_relat_1(k6_relat_1(sK0)),k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl4_18 | ~spl4_37)),
% 1.81/0.62    inference(subsumption_resolution,[],[f702,f208])).
% 1.81/0.62  fof(f702,plain,(
% 1.81/0.62    r1_tarski(k1_relat_1(k6_relat_1(sK0)),k1_relat_1(sK2)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | ~spl4_37),
% 1.81/0.62    inference(superposition,[],[f92,f581])).
% 1.81/0.62  fof(f581,plain,(
% 1.81/0.62    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_37),
% 1.81/0.62    inference(avatar_component_clause,[],[f579])).
% 1.81/0.62  fof(f92,plain,(
% 1.81/0.62    ( ! [X0,X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f44])).
% 1.81/0.62  fof(f44,plain,(
% 1.81/0.62    ! [X0] : (! [X1] : (r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.81/0.62    inference(ennf_transformation,[],[f9])).
% 1.81/0.62  fof(f9,axiom,(
% 1.81/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k1_relat_1(k5_relat_1(X0,X1)),k1_relat_1(X0))))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_relat_1)).
% 1.81/0.62  fof(f717,plain,(
% 1.81/0.62    spl4_42 | ~spl4_18 | ~spl4_19 | ~spl4_37),
% 1.81/0.62    inference(avatar_split_clause,[],[f712,f579,f212,f206,f714])).
% 1.81/0.62  fof(f712,plain,(
% 1.81/0.62    r1_tarski(sK0,k2_relat_1(sK3)) | (~spl4_18 | ~spl4_19 | ~spl4_37)),
% 1.81/0.62    inference(forward_demodulation,[],[f711,f84])).
% 1.81/0.62  fof(f84,plain,(
% 1.81/0.62    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.81/0.62    inference(cnf_transformation,[],[f11])).
% 1.81/0.62  fof(f711,plain,(
% 1.81/0.62    r1_tarski(k2_relat_1(k6_relat_1(sK0)),k2_relat_1(sK3)) | (~spl4_18 | ~spl4_19 | ~spl4_37)),
% 1.81/0.62    inference(subsumption_resolution,[],[f710,f214])).
% 1.81/0.62  fof(f710,plain,(
% 1.81/0.62    r1_tarski(k2_relat_1(k6_relat_1(sK0)),k2_relat_1(sK3)) | ~v1_relat_1(sK2) | (~spl4_18 | ~spl4_37)),
% 1.81/0.62    inference(subsumption_resolution,[],[f701,f208])).
% 1.81/0.62  fof(f701,plain,(
% 1.81/0.62    r1_tarski(k2_relat_1(k6_relat_1(sK0)),k2_relat_1(sK3)) | ~v1_relat_1(sK3) | ~v1_relat_1(sK2) | ~spl4_37),
% 1.81/0.62    inference(superposition,[],[f88,f581])).
% 1.81/0.62  fof(f88,plain,(
% 1.81/0.62    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f40])).
% 1.81/0.62  fof(f40,plain,(
% 1.81/0.62    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.81/0.62    inference(ennf_transformation,[],[f10])).
% 1.81/0.62  fof(f10,axiom,(
% 1.81/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 1.81/0.62  fof(f688,plain,(
% 1.81/0.62    spl4_1 | spl4_41 | ~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_35),
% 1.81/0.62    inference(avatar_split_clause,[],[f687,f570,f140,f135,f130,f125,f120,f115,f675,f101])).
% 1.81/0.62  fof(f115,plain,(
% 1.81/0.62    spl4_4 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 1.81/0.62  fof(f120,plain,(
% 1.81/0.62    spl4_5 <=> v1_funct_2(sK3,sK1,sK0)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.81/0.62  fof(f125,plain,(
% 1.81/0.62    spl4_6 <=> v1_funct_1(sK3)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 1.81/0.62  fof(f130,plain,(
% 1.81/0.62    spl4_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 1.81/0.62  fof(f135,plain,(
% 1.81/0.62    spl4_8 <=> v1_funct_2(sK2,sK0,sK1)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 1.81/0.62  fof(f140,plain,(
% 1.81/0.62    spl4_9 <=> v1_funct_1(sK2)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 1.81/0.62  fof(f570,plain,(
% 1.81/0.62    spl4_35 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_35])])).
% 1.81/0.62  fof(f687,plain,(
% 1.81/0.62    k1_xboole_0 = sK0 | v2_funct_1(sK2) | (~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_35)),
% 1.81/0.62    inference(subsumption_resolution,[],[f686,f142])).
% 1.81/0.62  fof(f142,plain,(
% 1.81/0.62    v1_funct_1(sK2) | ~spl4_9),
% 1.81/0.62    inference(avatar_component_clause,[],[f140])).
% 1.81/0.62  fof(f686,plain,(
% 1.81/0.62    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_35)),
% 1.81/0.62    inference(subsumption_resolution,[],[f685,f137])).
% 1.81/0.62  fof(f137,plain,(
% 1.81/0.62    v1_funct_2(sK2,sK0,sK1) | ~spl4_8),
% 1.81/0.62    inference(avatar_component_clause,[],[f135])).
% 1.81/0.62  fof(f685,plain,(
% 1.81/0.62    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_7 | ~spl4_35)),
% 1.81/0.62    inference(subsumption_resolution,[],[f684,f132])).
% 1.81/0.62  fof(f132,plain,(
% 1.81/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_7),
% 1.81/0.62    inference(avatar_component_clause,[],[f130])).
% 1.81/0.62  fof(f684,plain,(
% 1.81/0.62    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_5 | ~spl4_6 | ~spl4_35)),
% 1.81/0.62    inference(subsumption_resolution,[],[f683,f127])).
% 1.81/0.62  fof(f127,plain,(
% 1.81/0.62    v1_funct_1(sK3) | ~spl4_6),
% 1.81/0.62    inference(avatar_component_clause,[],[f125])).
% 1.81/0.62  fof(f683,plain,(
% 1.81/0.62    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_5 | ~spl4_35)),
% 1.81/0.62    inference(subsumption_resolution,[],[f682,f122])).
% 1.81/0.62  fof(f122,plain,(
% 1.81/0.62    v1_funct_2(sK3,sK1,sK0) | ~spl4_5),
% 1.81/0.62    inference(avatar_component_clause,[],[f120])).
% 1.81/0.62  fof(f682,plain,(
% 1.81/0.62    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_35)),
% 1.81/0.62    inference(subsumption_resolution,[],[f666,f117])).
% 1.81/0.62  fof(f117,plain,(
% 1.81/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_4),
% 1.81/0.62    inference(avatar_component_clause,[],[f115])).
% 1.81/0.62  fof(f666,plain,(
% 1.81/0.62    k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_35),
% 1.81/0.62    inference(subsumption_resolution,[],[f646,f67])).
% 1.81/0.62  fof(f67,plain,(
% 1.81/0.62    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.81/0.62    inference(cnf_transformation,[],[f13])).
% 1.81/0.62  fof(f13,axiom,(
% 1.81/0.62    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.81/0.62  fof(f646,plain,(
% 1.81/0.62    ~v2_funct_1(k6_relat_1(sK0)) | k1_xboole_0 = sK0 | v2_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_35),
% 1.81/0.62    inference(superposition,[],[f64,f572])).
% 1.81/0.62  fof(f572,plain,(
% 1.81/0.62    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~spl4_35),
% 1.81/0.62    inference(avatar_component_clause,[],[f570])).
% 1.81/0.62  fof(f64,plain,(
% 1.81/0.62    ( ! [X4,X2,X0,X3,X1] : (~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k1_xboole_0 = X2 | v2_funct_1(X3) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f29])).
% 1.81/0.62  fof(f29,plain,(
% 1.81/0.62    ! [X0,X1,X2,X3] : (! [X4] : (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 1.81/0.62    inference(flattening,[],[f28])).
% 1.81/0.62  fof(f28,plain,(
% 1.81/0.62    ! [X0,X1,X2,X3] : (! [X4] : (((v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 1.81/0.62    inference(ennf_transformation,[],[f21])).
% 1.81/0.62  fof(f21,axiom,(
% 1.81/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => (v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) => (v2_funct_1(X3) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_funct_2)).
% 1.81/0.62  fof(f656,plain,(
% 1.81/0.62    spl4_37 | ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_9 | ~spl4_35),
% 1.81/0.62    inference(avatar_split_clause,[],[f655,f570,f140,f130,f125,f115,f579])).
% 1.81/0.62  fof(f655,plain,(
% 1.81/0.62    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | (~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_9 | ~spl4_35)),
% 1.81/0.62    inference(subsumption_resolution,[],[f654,f142])).
% 1.81/0.62  fof(f654,plain,(
% 1.81/0.62    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_35)),
% 1.81/0.62    inference(subsumption_resolution,[],[f653,f132])).
% 1.81/0.62  fof(f653,plain,(
% 1.81/0.62    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6 | ~spl4_35)),
% 1.81/0.62    inference(subsumption_resolution,[],[f652,f127])).
% 1.81/0.62  fof(f652,plain,(
% 1.81/0.62    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_35)),
% 1.81/0.62    inference(subsumption_resolution,[],[f644,f117])).
% 1.81/0.62  fof(f644,plain,(
% 1.81/0.62    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_35),
% 1.81/0.62    inference(superposition,[],[f73,f572])).
% 1.81/0.62  fof(f73,plain,(
% 1.81/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f35])).
% 1.81/0.62  fof(f35,plain,(
% 1.81/0.62    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.81/0.62    inference(flattening,[],[f34])).
% 1.81/0.62  fof(f34,plain,(
% 1.81/0.62    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.81/0.62    inference(ennf_transformation,[],[f19])).
% 1.81/0.62  fof(f19,axiom,(
% 1.81/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.81/0.62  fof(f611,plain,(
% 1.81/0.62    ~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_9 | spl4_34),
% 1.81/0.62    inference(avatar_contradiction_clause,[],[f610])).
% 1.81/0.62  fof(f610,plain,(
% 1.81/0.62    $false | (~spl4_4 | ~spl4_6 | ~spl4_7 | ~spl4_9 | spl4_34)),
% 1.81/0.62    inference(subsumption_resolution,[],[f609,f142])).
% 1.81/0.62  fof(f609,plain,(
% 1.81/0.62    ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6 | ~spl4_7 | spl4_34)),
% 1.81/0.62    inference(subsumption_resolution,[],[f608,f132])).
% 1.81/0.62  fof(f608,plain,(
% 1.81/0.62    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_4 | ~spl4_6 | spl4_34)),
% 1.81/0.62    inference(subsumption_resolution,[],[f607,f127])).
% 1.81/0.62  fof(f607,plain,(
% 1.81/0.62    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_4 | spl4_34)),
% 1.81/0.62    inference(subsumption_resolution,[],[f604,f117])).
% 1.81/0.62  fof(f604,plain,(
% 1.81/0.62    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_34),
% 1.81/0.62    inference(resolution,[],[f568,f72])).
% 1.81/0.62  fof(f72,plain,(
% 1.81/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f33])).
% 1.81/0.62  fof(f33,plain,(
% 1.81/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.81/0.62    inference(flattening,[],[f32])).
% 1.81/0.62  fof(f32,plain,(
% 1.81/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.81/0.62    inference(ennf_transformation,[],[f18])).
% 1.81/0.62  fof(f18,axiom,(
% 1.81/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.81/0.62  fof(f568,plain,(
% 1.81/0.62    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_34),
% 1.81/0.62    inference(avatar_component_clause,[],[f566])).
% 1.81/0.62  fof(f566,plain,(
% 1.81/0.62    spl4_34 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_34])])).
% 1.81/0.62  fof(f573,plain,(
% 1.81/0.62    ~spl4_34 | spl4_35 | ~spl4_14),
% 1.81/0.62    inference(avatar_split_clause,[],[f561,f168,f570,f566])).
% 1.81/0.62  fof(f168,plain,(
% 1.81/0.62    spl4_14 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 1.81/0.62  fof(f561,plain,(
% 1.81/0.62    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_14),
% 1.81/0.62    inference(resolution,[],[f327,f170])).
% 1.81/0.62  fof(f170,plain,(
% 1.81/0.62    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_14),
% 1.81/0.62    inference(avatar_component_clause,[],[f168])).
% 1.81/0.62  fof(f327,plain,(
% 1.81/0.62    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 1.81/0.62    inference(resolution,[],[f68,f77])).
% 1.81/0.62  fof(f77,plain,(
% 1.81/0.62    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.81/0.62    inference(cnf_transformation,[],[f16])).
% 1.81/0.62  fof(f16,axiom,(
% 1.81/0.62    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 1.81/0.62  fof(f68,plain,(
% 1.81/0.62    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.81/0.62    inference(cnf_transformation,[],[f49])).
% 1.81/0.62  fof(f49,plain,(
% 1.81/0.62    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.62    inference(nnf_transformation,[],[f31])).
% 1.81/0.62  fof(f31,plain,(
% 1.81/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.62    inference(flattening,[],[f30])).
% 1.81/0.62  fof(f30,plain,(
% 1.81/0.62    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.81/0.62    inference(ennf_transformation,[],[f15])).
% 1.81/0.62  fof(f15,axiom,(
% 1.81/0.62    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.81/0.62  fof(f236,plain,(
% 1.81/0.62    spl4_22 | ~spl4_4),
% 1.81/0.62    inference(avatar_split_clause,[],[f229,f115,f233])).
% 1.81/0.62  fof(f229,plain,(
% 1.81/0.62    v5_relat_1(sK3,sK0) | ~spl4_4),
% 1.81/0.62    inference(resolution,[],[f75,f117])).
% 1.81/0.62  fof(f75,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v5_relat_1(X2,X1)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f36])).
% 1.81/0.62  fof(f36,plain,(
% 1.81/0.62    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.81/0.62    inference(ennf_transformation,[],[f14])).
% 1.81/0.62  fof(f14,axiom,(
% 1.81/0.62    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.81/0.62  fof(f228,plain,(
% 1.81/0.62    spl4_21 | ~spl4_7),
% 1.81/0.62    inference(avatar_split_clause,[],[f217,f130,f225])).
% 1.81/0.62  fof(f217,plain,(
% 1.81/0.62    v4_relat_1(sK2,sK0) | ~spl4_7),
% 1.81/0.62    inference(resolution,[],[f74,f132])).
% 1.81/0.62  fof(f74,plain,(
% 1.81/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f36])).
% 1.81/0.62  fof(f215,plain,(
% 1.81/0.62    spl4_19 | ~spl4_7),
% 1.81/0.62    inference(avatar_split_clause,[],[f210,f130,f212])).
% 1.81/0.62  fof(f210,plain,(
% 1.81/0.62    v1_relat_1(sK2) | ~spl4_7),
% 1.81/0.62    inference(subsumption_resolution,[],[f202,f78])).
% 1.81/0.62  fof(f78,plain,(
% 1.81/0.62    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.81/0.62    inference(cnf_transformation,[],[f7])).
% 1.81/0.62  fof(f7,axiom,(
% 1.81/0.62    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.81/0.62  fof(f202,plain,(
% 1.81/0.62    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl4_7),
% 1.81/0.62    inference(resolution,[],[f76,f132])).
% 1.81/0.62  fof(f76,plain,(
% 1.81/0.62    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f37])).
% 1.81/0.62  fof(f37,plain,(
% 1.81/0.62    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.81/0.62    inference(ennf_transformation,[],[f4])).
% 1.81/0.62  fof(f4,axiom,(
% 1.81/0.62    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.81/0.62  fof(f209,plain,(
% 1.81/0.62    spl4_18 | ~spl4_4),
% 1.81/0.62    inference(avatar_split_clause,[],[f204,f115,f206])).
% 1.81/0.62  fof(f204,plain,(
% 1.81/0.62    v1_relat_1(sK3) | ~spl4_4),
% 1.81/0.62    inference(subsumption_resolution,[],[f201,f78])).
% 1.81/0.62  fof(f201,plain,(
% 1.81/0.62    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | ~spl4_4),
% 1.81/0.62    inference(resolution,[],[f76,f117])).
% 1.81/0.62  fof(f171,plain,(
% 1.81/0.62    spl4_14 | ~spl4_3),
% 1.81/0.62    inference(avatar_split_clause,[],[f166,f110,f168])).
% 1.81/0.62  fof(f110,plain,(
% 1.81/0.62    spl4_3 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 1.81/0.62  fof(f166,plain,(
% 1.81/0.62    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_3),
% 1.81/0.62    inference(backward_demodulation,[],[f112,f70])).
% 1.81/0.62  fof(f70,plain,(
% 1.81/0.62    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.81/0.62    inference(cnf_transformation,[],[f20])).
% 1.81/0.62  fof(f20,axiom,(
% 1.81/0.62    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.81/0.62  fof(f112,plain,(
% 1.81/0.62    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_3),
% 1.81/0.62    inference(avatar_component_clause,[],[f110])).
% 1.81/0.62  fof(f160,plain,(
% 1.81/0.62    spl4_12 | ~spl4_10),
% 1.81/0.62    inference(avatar_split_clause,[],[f154,f145,f157])).
% 1.81/0.62  fof(f145,plain,(
% 1.81/0.62    spl4_10 <=> k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.81/0.62    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 1.81/0.62  fof(f154,plain,(
% 1.81/0.62    v2_funct_1(k1_xboole_0) | ~spl4_10),
% 1.81/0.62    inference(superposition,[],[f67,f147])).
% 1.81/0.62  fof(f147,plain,(
% 1.81/0.62    k1_xboole_0 = k6_relat_1(k1_xboole_0) | ~spl4_10),
% 1.81/0.62    inference(avatar_component_clause,[],[f145])).
% 1.81/0.62  fof(f153,plain,(
% 1.81/0.62    spl4_11),
% 1.81/0.62    inference(avatar_split_clause,[],[f93,f150])).
% 1.81/0.62  fof(f93,plain,(
% 1.81/0.62    v1_xboole_0(k1_xboole_0)),
% 1.81/0.62    inference(cnf_transformation,[],[f1])).
% 1.81/0.62  fof(f1,axiom,(
% 1.81/0.62    v1_xboole_0(k1_xboole_0)),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.81/0.62  fof(f148,plain,(
% 1.81/0.62    spl4_10),
% 1.81/0.62    inference(avatar_split_clause,[],[f85,f145])).
% 1.81/0.62  fof(f85,plain,(
% 1.81/0.62    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.81/0.62    inference(cnf_transformation,[],[f12])).
% 1.81/0.62  fof(f12,axiom,(
% 1.81/0.62    k1_xboole_0 = k6_relat_1(k1_xboole_0)),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_relat_1)).
% 1.81/0.62  fof(f143,plain,(
% 1.81/0.62    spl4_9),
% 1.81/0.62    inference(avatar_split_clause,[],[f54,f140])).
% 1.81/0.62  fof(f54,plain,(
% 1.81/0.62    v1_funct_1(sK2)),
% 1.81/0.62    inference(cnf_transformation,[],[f47])).
% 1.81/0.62  fof(f47,plain,(
% 1.81/0.62    ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.81/0.62    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f25,f46,f45])).
% 1.81/0.62  fof(f45,plain,(
% 1.81/0.62    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.81/0.62    introduced(choice_axiom,[])).
% 1.81/0.62  fof(f46,plain,(
% 1.81/0.62    ? [X3] : ((~v2_funct_2(X3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => ((~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.81/0.62    introduced(choice_axiom,[])).
% 1.81/0.62  fof(f25,plain,(
% 1.81/0.62    ? [X0,X1,X2] : (? [X3] : ((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.81/0.62    inference(flattening,[],[f24])).
% 1.81/0.62  fof(f24,plain,(
% 1.81/0.62    ? [X0,X1,X2] : (? [X3] : (((~v2_funct_2(X3,X0) | ~v2_funct_1(X2)) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.81/0.62    inference(ennf_transformation,[],[f23])).
% 1.81/0.62  fof(f23,negated_conjecture,(
% 1.81/0.62    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.81/0.62    inference(negated_conjecture,[],[f22])).
% 1.81/0.62  fof(f22,conjecture,(
% 1.81/0.62    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) => (v2_funct_2(X3,X0) & v2_funct_1(X2)))))),
% 1.81/0.62    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_funct_2)).
% 1.81/0.62  fof(f138,plain,(
% 1.81/0.62    spl4_8),
% 1.81/0.62    inference(avatar_split_clause,[],[f55,f135])).
% 1.81/0.62  fof(f55,plain,(
% 1.81/0.62    v1_funct_2(sK2,sK0,sK1)),
% 1.81/0.62    inference(cnf_transformation,[],[f47])).
% 1.81/0.62  fof(f133,plain,(
% 1.81/0.62    spl4_7),
% 1.81/0.62    inference(avatar_split_clause,[],[f56,f130])).
% 1.81/0.62  fof(f56,plain,(
% 1.81/0.62    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.81/0.62    inference(cnf_transformation,[],[f47])).
% 1.81/0.62  fof(f128,plain,(
% 1.81/0.62    spl4_6),
% 1.81/0.62    inference(avatar_split_clause,[],[f57,f125])).
% 1.81/0.62  fof(f57,plain,(
% 1.81/0.62    v1_funct_1(sK3)),
% 1.81/0.62    inference(cnf_transformation,[],[f47])).
% 1.81/0.62  fof(f123,plain,(
% 1.81/0.62    spl4_5),
% 1.81/0.62    inference(avatar_split_clause,[],[f58,f120])).
% 1.81/0.62  fof(f58,plain,(
% 1.81/0.62    v1_funct_2(sK3,sK1,sK0)),
% 1.81/0.62    inference(cnf_transformation,[],[f47])).
% 1.81/0.62  fof(f118,plain,(
% 1.81/0.62    spl4_4),
% 1.81/0.62    inference(avatar_split_clause,[],[f59,f115])).
% 1.81/0.62  fof(f59,plain,(
% 1.81/0.62    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.81/0.62    inference(cnf_transformation,[],[f47])).
% 1.81/0.62  fof(f113,plain,(
% 1.81/0.62    spl4_3),
% 1.81/0.62    inference(avatar_split_clause,[],[f60,f110])).
% 1.81/0.62  fof(f60,plain,(
% 1.81/0.62    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.81/0.62    inference(cnf_transformation,[],[f47])).
% 1.81/0.62  fof(f108,plain,(
% 1.81/0.62    ~spl4_1 | ~spl4_2),
% 1.81/0.62    inference(avatar_split_clause,[],[f61,f105,f101])).
% 1.81/0.62  fof(f61,plain,(
% 1.81/0.62    ~v2_funct_2(sK3,sK0) | ~v2_funct_1(sK2)),
% 1.81/0.62    inference(cnf_transformation,[],[f47])).
% 1.81/0.62  % SZS output end Proof for theBenchmark
% 1.81/0.62  % (20953)------------------------------
% 1.81/0.62  % (20953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.81/0.62  % (20953)Termination reason: Refutation
% 1.81/0.62  
% 1.81/0.62  % (20953)Memory used [KB]: 7291
% 1.81/0.62  % (20953)Time elapsed: 0.189 s
% 1.81/0.62  % (20953)------------------------------
% 1.81/0.62  % (20953)------------------------------
% 2.01/0.63  % (20931)Success in time 0.259 s
%------------------------------------------------------------------------------
