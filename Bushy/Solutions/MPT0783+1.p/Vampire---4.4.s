%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : wellord1__t32_wellord1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:41:13 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :  106 ( 590 expanded)
%              Number of leaves         :   17 ( 191 expanded)
%              Depth                    :   13
%              Number of atoms          :  445 (2025 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f162,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f63,f70,f78,f86,f94,f102,f110,f142,f144,f146,f148,f150,f152,f154,f161])).

fof(f161,plain,
    ( ~ spl2_0
    | spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(avatar_contradiction_clause,[],[f160])).

fof(f160,plain,
    ( $false
    | ~ spl2_0
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f159,f111])).

fof(f111,plain,
    ( ! [X0] : v1_relat_1(k2_wellord1(sK1,X0))
    | ~ spl2_0 ),
    inference(unit_resulting_resolution,[],[f55,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k2_wellord1(X0,X1))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X0)
     => v1_relat_1(k2_wellord1(X0,X1)) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t32_wellord1.p',dt_k2_wellord1)).

fof(f55,plain,
    ( v1_relat_1(sK1)
    | ~ spl2_0 ),
    inference(avatar_component_clause,[],[f54])).

fof(f54,plain,
    ( spl2_0
  <=> v1_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_0])])).

fof(f159,plain,
    ( ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | ~ spl2_0
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f158,f119])).

fof(f119,plain,
    ( ! [X0] : v1_relat_2(k2_wellord1(sK1,X0))
    | ~ spl2_0
    | ~ spl2_6 ),
    inference(unit_resulting_resolution,[],[f55,f77,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( v1_relat_2(k2_wellord1(X1,X0))
      | ~ v1_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( v1_relat_2(k2_wellord1(X1,X0))
      | ~ v1_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( v1_relat_2(k2_wellord1(X1,X0))
      | ~ v1_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v1_relat_2(X1)
       => v1_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t32_wellord1.p',t22_wellord1)).

fof(f77,plain,
    ( v1_relat_2(sK1)
    | ~ spl2_6 ),
    inference(avatar_component_clause,[],[f76])).

fof(f76,plain,
    ( spl2_6
  <=> v1_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_6])])).

fof(f158,plain,
    ( ~ v1_relat_2(k2_wellord1(sK1,sK0))
    | ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | ~ spl2_0
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f157,f125])).

fof(f125,plain,
    ( ! [X0] : v8_relat_2(k2_wellord1(sK1,X0))
    | ~ spl2_0
    | ~ spl2_8 ),
    inference(unit_resulting_resolution,[],[f55,f85,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v8_relat_2(k2_wellord1(X1,X0))
      | ~ v8_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( v8_relat_2(k2_wellord1(X1,X0))
      | ~ v8_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( v8_relat_2(k2_wellord1(X1,X0))
      | ~ v8_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v8_relat_2(X1)
       => v8_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t32_wellord1.p',t24_wellord1)).

fof(f85,plain,
    ( v8_relat_2(sK1)
    | ~ spl2_8 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl2_8
  <=> v8_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_8])])).

fof(f157,plain,
    ( ~ v8_relat_2(k2_wellord1(sK1,sK0))
    | ~ v1_relat_2(k2_wellord1(sK1,sK0))
    | ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | ~ spl2_0
    | ~ spl2_5
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f156,f114])).

fof(f114,plain,
    ( ! [X0] : v4_relat_2(k2_wellord1(sK1,X0))
    | ~ spl2_0
    | ~ spl2_10 ),
    inference(unit_resulting_resolution,[],[f55,f93,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v4_relat_2(k2_wellord1(X1,X0))
      | ~ v4_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( v4_relat_2(k2_wellord1(X1,X0))
      | ~ v4_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( v4_relat_2(k2_wellord1(X1,X0))
      | ~ v4_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_2(X1)
       => v4_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t32_wellord1.p',t25_wellord1)).

fof(f93,plain,
    ( v4_relat_2(sK1)
    | ~ spl2_10 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl2_10
  <=> v4_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_10])])).

fof(f156,plain,
    ( ~ v4_relat_2(k2_wellord1(sK1,sK0))
    | ~ v8_relat_2(k2_wellord1(sK1,sK0))
    | ~ v1_relat_2(k2_wellord1(sK1,sK0))
    | ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | ~ spl2_0
    | ~ spl2_5
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f155,f123])).

fof(f123,plain,
    ( ! [X0] : v6_relat_2(k2_wellord1(sK1,X0))
    | ~ spl2_0
    | ~ spl2_12 ),
    inference(unit_resulting_resolution,[],[f55,f101,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v6_relat_2(k2_wellord1(X1,X0))
      | ~ v6_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v6_relat_2(k2_wellord1(X1,X0))
      | ~ v6_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v6_relat_2(k2_wellord1(X1,X0))
      | ~ v6_relat_2(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v6_relat_2(X1)
       => v6_relat_2(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t32_wellord1.p',t23_wellord1)).

fof(f101,plain,
    ( v6_relat_2(sK1)
    | ~ spl2_12 ),
    inference(avatar_component_clause,[],[f100])).

fof(f100,plain,
    ( spl2_12
  <=> v6_relat_2(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_12])])).

fof(f155,plain,
    ( ~ v6_relat_2(k2_wellord1(sK1,sK0))
    | ~ v4_relat_2(k2_wellord1(sK1,sK0))
    | ~ v8_relat_2(k2_wellord1(sK1,sK0))
    | ~ v1_relat_2(k2_wellord1(sK1,sK0))
    | ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | ~ spl2_0
    | ~ spl2_5
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f141,f117])).

fof(f117,plain,
    ( ! [X0] : v1_wellord1(k2_wellord1(sK1,X0))
    | ~ spl2_0
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f55,f109,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v1_wellord1(k2_wellord1(X1,X0))
      | ~ v1_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( v1_wellord1(k2_wellord1(X1,X0))
      | ~ v1_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( v1_wellord1(k2_wellord1(X1,X0))
      | ~ v1_wellord1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v1_wellord1(X1)
       => v1_wellord1(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t32_wellord1.p',t31_wellord1)).

fof(f109,plain,
    ( v1_wellord1(sK1)
    | ~ spl2_14 ),
    inference(avatar_component_clause,[],[f108])).

fof(f108,plain,
    ( spl2_14
  <=> v1_wellord1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_14])])).

fof(f141,plain,
    ( ~ v1_wellord1(k2_wellord1(sK1,sK0))
    | ~ v6_relat_2(k2_wellord1(sK1,sK0))
    | ~ v4_relat_2(k2_wellord1(sK1,sK0))
    | ~ v8_relat_2(k2_wellord1(sK1,sK0))
    | ~ v1_relat_2(k2_wellord1(sK1,sK0))
    | ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | ~ spl2_5 ),
    inference(resolution,[],[f41,f69])).

fof(f69,plain,
    ( ~ v2_wellord1(k2_wellord1(sK1,sK0))
    | ~ spl2_5 ),
    inference(avatar_component_clause,[],[f68])).

fof(f68,plain,
    ( spl2_5
  <=> ~ v2_wellord1(k2_wellord1(sK1,sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_5])])).

fof(f41,plain,(
    ! [X0] :
      ( v2_wellord1(X0)
      | ~ v1_wellord1(X0)
      | ~ v6_relat_2(X0)
      | ~ v4_relat_2(X0)
      | ~ v8_relat_2(X0)
      | ~ v1_relat_2(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( ( v2_wellord1(X0)
          | ~ v1_wellord1(X0)
          | ~ v6_relat_2(X0)
          | ~ v4_relat_2(X0)
          | ~ v8_relat_2(X0)
          | ~ v1_relat_2(X0) )
        & ( ( v1_wellord1(X0)
            & v6_relat_2(X0)
            & v4_relat_2(X0)
            & v8_relat_2(X0)
            & v1_relat_2(X0) )
          | ~ v2_wellord1(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(nnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( v2_wellord1(X0)
      <=> ( v1_wellord1(X0)
          & v6_relat_2(X0)
          & v4_relat_2(X0)
          & v8_relat_2(X0)
          & v1_relat_2(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t32_wellord1.p',d4_wellord1)).

fof(f154,plain,
    ( ~ spl2_0
    | spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(avatar_contradiction_clause,[],[f153])).

fof(f153,plain,
    ( $false
    | ~ spl2_0
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f134,f117])).

fof(f134,plain,
    ( ~ v1_wellord1(k2_wellord1(sK1,sK0))
    | ~ spl2_0
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_12 ),
    inference(unit_resulting_resolution,[],[f111,f119,f125,f114,f123,f69,f41])).

fof(f152,plain,
    ( ~ spl2_0
    | spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(avatar_contradiction_clause,[],[f151])).

fof(f151,plain,
    ( $false
    | ~ spl2_0
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f135,f123])).

fof(f135,plain,
    ( ~ v6_relat_2(k2_wellord1(sK1,sK0))
    | ~ spl2_0
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f111,f119,f125,f114,f117,f69,f41])).

fof(f150,plain,
    ( ~ spl2_0
    | spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | ~ spl2_0
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f136,f114])).

fof(f136,plain,
    ( ~ v4_relat_2(k2_wellord1(sK1,sK0))
    | ~ spl2_0
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f111,f119,f125,f123,f117,f69,f41])).

fof(f148,plain,
    ( ~ spl2_0
    | spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(avatar_contradiction_clause,[],[f147])).

fof(f147,plain,
    ( $false
    | ~ spl2_0
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f137,f125])).

fof(f137,plain,
    ( ~ v8_relat_2(k2_wellord1(sK1,sK0))
    | ~ spl2_0
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f111,f119,f114,f123,f117,f69,f41])).

fof(f146,plain,
    ( ~ spl2_0
    | spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | ~ spl2_0
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f138,f119])).

fof(f138,plain,
    ( ~ v1_relat_2(k2_wellord1(sK1,sK0))
    | ~ spl2_0
    | ~ spl2_5
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f111,f125,f114,f123,f117,f69,f41])).

fof(f144,plain,
    ( ~ spl2_0
    | spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(avatar_contradiction_clause,[],[f143])).

fof(f143,plain,
    ( $false
    | ~ spl2_0
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(subsumption_resolution,[],[f139,f111])).

fof(f139,plain,
    ( ~ v1_relat_1(k2_wellord1(sK1,sK0))
    | ~ spl2_0
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f119,f125,f114,f123,f117,f69,f41])).

fof(f142,plain,
    ( ~ spl2_0
    | spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(avatar_contradiction_clause,[],[f140])).

fof(f140,plain,
    ( $false
    | ~ spl2_0
    | ~ spl2_5
    | ~ spl2_6
    | ~ spl2_8
    | ~ spl2_10
    | ~ spl2_12
    | ~ spl2_14 ),
    inference(unit_resulting_resolution,[],[f111,f119,f125,f114,f123,f117,f69,f41])).

fof(f110,plain,
    ( spl2_14
    | ~ spl2_0
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f103,f61,f54,f108])).

fof(f61,plain,
    ( spl2_2
  <=> v2_wellord1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl2_2])])).

fof(f103,plain,
    ( v1_wellord1(sK1)
    | ~ spl2_0
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f55,f62,f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_wellord1(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f62,plain,
    ( v2_wellord1(sK1)
    | ~ spl2_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f102,plain,
    ( spl2_12
    | ~ spl2_0
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f95,f61,f54,f100])).

fof(f95,plain,
    ( v6_relat_2(sK1)
    | ~ spl2_0
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f55,f62,f39])).

fof(f39,plain,(
    ! [X0] :
      ( v6_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f94,plain,
    ( spl2_10
    | ~ spl2_0
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f87,f61,f54,f92])).

fof(f87,plain,
    ( v4_relat_2(sK1)
    | ~ spl2_0
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f55,f62,f38])).

fof(f38,plain,(
    ! [X0] :
      ( v4_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f86,plain,
    ( spl2_8
    | ~ spl2_0
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f79,f61,f54,f84])).

fof(f79,plain,
    ( v8_relat_2(sK1)
    | ~ spl2_0
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f55,f62,f37])).

fof(f37,plain,(
    ! [X0] :
      ( v8_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f78,plain,
    ( spl2_6
    | ~ spl2_0
    | ~ spl2_2 ),
    inference(avatar_split_clause,[],[f71,f61,f54,f76])).

fof(f71,plain,
    ( v1_relat_2(sK1)
    | ~ spl2_0
    | ~ spl2_2 ),
    inference(unit_resulting_resolution,[],[f55,f62,f36])).

fof(f36,plain,(
    ! [X0] :
      ( v1_relat_2(X0)
      | ~ v2_wellord1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f70,plain,(
    ~ spl2_5 ),
    inference(avatar_split_clause,[],[f35,f68])).

fof(f35,plain,(
    ~ v2_wellord1(k2_wellord1(sK1,sK0)) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,
    ( ~ v2_wellord1(k2_wellord1(sK1,sK0))
    & v2_wellord1(sK1)
    & v1_relat_1(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1])],[f16,f29])).

fof(f29,plain,
    ( ? [X0,X1] :
        ( ~ v2_wellord1(k2_wellord1(X1,X0))
        & v2_wellord1(X1)
        & v1_relat_1(X1) )
   => ( ~ v2_wellord1(k2_wellord1(sK1,sK0))
      & v2_wellord1(sK1)
      & v1_relat_1(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f16,plain,(
    ? [X0,X1] :
      ( ~ v2_wellord1(k2_wellord1(X1,X0))
      & v2_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0,X1] :
      ( ~ v2_wellord1(k2_wellord1(X1,X0))
      & v2_wellord1(X1)
      & v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( v1_relat_1(X1)
       => ( v2_wellord1(X1)
         => v2_wellord1(k2_wellord1(X1,X0)) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v2_wellord1(X1)
       => v2_wellord1(k2_wellord1(X1,X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/wellord1__t32_wellord1.p',t32_wellord1)).

fof(f63,plain,(
    spl2_2 ),
    inference(avatar_split_clause,[],[f34,f61])).

fof(f34,plain,(
    v2_wellord1(sK1) ),
    inference(cnf_transformation,[],[f30])).

fof(f56,plain,(
    spl2_0 ),
    inference(avatar_split_clause,[],[f33,f54])).

fof(f33,plain,(
    v1_relat_1(sK1) ),
    inference(cnf_transformation,[],[f30])).
%------------------------------------------------------------------------------
