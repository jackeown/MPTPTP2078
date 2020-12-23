%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1732+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:26 EST 2020

% Result     : Theorem 2.07s
% Output     : Refutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :  220 ( 525 expanded)
%              Number of leaves         :   53 ( 249 expanded)
%              Depth                    :    9
%              Number of atoms          :  782 (2862 expanded)
%              Number of equality atoms :   37 (  64 expanded)
%              Maximal formula depth    :   17 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4835,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f89,f94,f99,f104,f114,f119,f124,f129,f134,f144,f175,f177,f179,f187,f195,f203,f291,f304,f323,f347,f357,f407,f412,f425,f608,f808,f813,f827,f1355,f1375,f2124,f4283,f4372,f4378,f4422,f4461,f4834])).

fof(f4834,plain,
    ( ~ spl6_36
    | spl6_239 ),
    inference(avatar_contradiction_clause,[],[f4833])).

fof(f4833,plain,
    ( $false
    | ~ spl6_36
    | spl6_239 ),
    inference(subsumption_resolution,[],[f2135,f4701])).

fof(f4701,plain,
    ( ! [X2] : r1_xboole_0(k3_xboole_0(u1_struct_0(sK3),X2),u1_struct_0(sK5))
    | ~ spl6_36 ),
    inference(superposition,[],[f2555,f66])).

fof(f66,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f2555,plain,
    ( ! [X44] : r1_xboole_0(k3_xboole_0(X44,u1_struct_0(sK3)),u1_struct_0(sK5))
    | ~ spl6_36 ),
    inference(subsumption_resolution,[],[f2530,f58])).

fof(f58,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f2530,plain,
    ( ! [X44] :
        ( k1_xboole_0 != k3_xboole_0(X44,k1_xboole_0)
        | r1_xboole_0(k3_xboole_0(X44,u1_struct_0(sK3)),u1_struct_0(sK5)) )
    | ~ spl6_36 ),
    inference(superposition,[],[f388,f424])).

fof(f424,plain,
    ( k1_xboole_0 = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5))
    | ~ spl6_36 ),
    inference(avatar_component_clause,[],[f422])).

fof(f422,plain,
    ( spl6_36
  <=> k1_xboole_0 = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_36])])).

fof(f388,plain,(
    ! [X14,X15,X13] :
      ( k1_xboole_0 != k3_xboole_0(X13,k3_xboole_0(X14,X15))
      | r1_xboole_0(k3_xboole_0(X13,X14),X15) ) ),
    inference(superposition,[],[f70,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(k3_xboole_0(X0,X1),X2) = k3_xboole_0(X0,k3_xboole_0(X1,X2)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

fof(f70,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) != k1_xboole_0
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f2135,plain,
    ( ~ r1_xboole_0(k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)),u1_struct_0(sK5))
    | spl6_239 ),
    inference(avatar_component_clause,[],[f2133])).

fof(f2133,plain,
    ( spl6_239
  <=> r1_xboole_0(k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_239])])).

fof(f4461,plain,
    ( ~ spl6_239
    | spl6_80
    | ~ spl6_237 ),
    inference(avatar_split_clause,[],[f4376,f2121,f824,f2133])).

fof(f824,plain,
    ( spl6_80
  <=> r1_xboole_0(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f2121,plain,
    ( spl6_237
  <=> u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_237])])).

fof(f4376,plain,
    ( ~ r1_xboole_0(k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)),u1_struct_0(sK5))
    | spl6_80
    | ~ spl6_237 ),
    inference(forward_demodulation,[],[f826,f2123])).

fof(f2123,plain,
    ( u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4))
    | ~ spl6_237 ),
    inference(avatar_component_clause,[],[f2121])).

fof(f826,plain,
    ( ~ r1_xboole_0(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),u1_struct_0(sK5))
    | spl6_80 ),
    inference(avatar_component_clause,[],[f824])).

fof(f4422,plain,
    ( spl6_23
    | spl6_24
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f445,f78,f285,f280])).

fof(f280,plain,
    ( spl6_23
  <=> r1_tsep_1(sK4,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f285,plain,
    ( spl6_24
  <=> r1_tsep_1(sK3,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f78,plain,
    ( spl6_1
  <=> sP0(sK5,sK4,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f445,plain,
    ( r1_tsep_1(sK3,sK5)
    | r1_tsep_1(sK4,sK5)
    | ~ spl6_1 ),
    inference(resolution,[],[f80,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_tsep_1(X2,X0)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r1_tsep_1(X1,X0)
          | r1_tsep_1(X2,X0) )
        & ~ r1_tsep_1(k2_tsep_1(X3,X2,X1),X0) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X3,X2,X1,X0] :
      ( ( ( r1_tsep_1(X2,X3)
          | r1_tsep_1(X1,X3) )
        & ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) )
      | ~ sP0(X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X3,X2,X1,X0] :
      ( ( ( r1_tsep_1(X2,X3)
          | r1_tsep_1(X1,X3) )
        & ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) )
      | ~ sP0(X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f80,plain,
    ( sP0(sK5,sK4,sK3,sK2)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f4378,plain,
    ( ~ spl6_42
    | spl6_80
    | ~ spl6_237 ),
    inference(avatar_contradiction_clause,[],[f4377])).

fof(f4377,plain,
    ( $false
    | ~ spl6_42
    | spl6_80
    | ~ spl6_237 ),
    inference(subsumption_resolution,[],[f4376,f4142])).

fof(f4142,plain,
    ( ! [X17] : r1_xboole_0(k3_xboole_0(X17,u1_struct_0(sK4)),u1_struct_0(sK5))
    | ~ spl6_42 ),
    inference(subsumption_resolution,[],[f4133,f58])).

fof(f4133,plain,
    ( ! [X17] :
        ( k1_xboole_0 != k3_xboole_0(X17,k1_xboole_0)
        | r1_xboole_0(k3_xboole_0(X17,u1_struct_0(sK4)),u1_struct_0(sK5)) )
    | ~ spl6_42 ),
    inference(superposition,[],[f388,f508])).

fof(f508,plain,
    ( k1_xboole_0 = k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ spl6_42 ),
    inference(avatar_component_clause,[],[f507])).

fof(f507,plain,
    ( spl6_42
  <=> k1_xboole_0 = k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_42])])).

fof(f4372,plain,
    ( spl6_34
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f530,f404,f409])).

fof(f409,plain,
    ( spl6_34
  <=> r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f404,plain,
    ( spl6_33
  <=> r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f530,plain,
    ( r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl6_33 ),
    inference(unit_resulting_resolution,[],[f406,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X1,X0)
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
     => r1_xboole_0(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

fof(f406,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5))
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f404])).

fof(f4283,plain,
    ( ~ spl6_26
    | ~ spl6_1 ),
    inference(avatar_split_clause,[],[f444,f78,f301])).

fof(f301,plain,
    ( spl6_26
  <=> r1_tsep_1(k2_tsep_1(sK2,sK3,sK4),sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f444,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK2,sK3,sK4),sK5)
    | ~ spl6_1 ),
    inference(unit_resulting_resolution,[],[f80,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(k2_tsep_1(X3,X2,X1),X0)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f2124,plain,
    ( spl6_237
    | spl6_5
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | spl6_14
    | ~ spl6_31
    | spl6_77
    | ~ spl6_78 ),
    inference(avatar_split_clause,[],[f1977,f810,f805,f344,f141,f131,f126,f121,f116,f111,f96,f2121])).

fof(f96,plain,
    ( spl6_5
  <=> r1_tsep_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f111,plain,
    ( spl6_8
  <=> m1_pre_topc(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f116,plain,
    ( spl6_9
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f121,plain,
    ( spl6_10
  <=> m1_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f126,plain,
    ( spl6_11
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f131,plain,
    ( spl6_12
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f141,plain,
    ( spl6_14
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f344,plain,
    ( spl6_31
  <=> m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f805,plain,
    ( spl6_77
  <=> v2_struct_0(k2_tsep_1(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_77])])).

fof(f810,plain,
    ( spl6_78
  <=> v1_pre_topc(k2_tsep_1(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f1977,plain,
    ( u1_struct_0(k2_tsep_1(sK2,sK3,sK4)) = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4))
    | spl6_5
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | spl6_14
    | ~ spl6_31
    | spl6_77
    | ~ spl6_78 ),
    inference(unit_resulting_resolution,[],[f143,f133,f128,f118,f123,f113,f98,f807,f812,f345,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k2_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( ( k2_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k2_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k2_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | r1_tsep_1(X1,X2)
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_tsep_1)).

fof(f345,plain,
    ( m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f344])).

fof(f812,plain,
    ( v1_pre_topc(k2_tsep_1(sK2,sK3,sK4))
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f810])).

fof(f807,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | spl6_77 ),
    inference(avatar_component_clause,[],[f805])).

fof(f98,plain,
    ( ~ r1_tsep_1(sK3,sK4)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f96])).

fof(f113,plain,
    ( m1_pre_topc(sK4,sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f111])).

fof(f123,plain,
    ( m1_pre_topc(sK3,sK2)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f121])).

fof(f118,plain,
    ( ~ v2_struct_0(sK4)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f116])).

fof(f128,plain,
    ( ~ v2_struct_0(sK3)
    | spl6_11 ),
    inference(avatar_component_clause,[],[f126])).

fof(f133,plain,
    ( l1_pre_topc(sK2)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f131])).

fof(f143,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_14 ),
    inference(avatar_component_clause,[],[f141])).

fof(f1375,plain,
    ( spl6_42
    | ~ spl6_38 ),
    inference(avatar_split_clause,[],[f1366,f481,f507])).

fof(f481,plain,
    ( spl6_38
  <=> r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f1366,plain,
    ( k1_xboole_0 = k3_xboole_0(u1_struct_0(sK4),u1_struct_0(sK5))
    | ~ spl6_38 ),
    inference(unit_resulting_resolution,[],[f482,f213])).

fof(f213,plain,(
    ! [X4,X5] :
      ( k1_xboole_0 = k3_xboole_0(X5,X4)
      | ~ r1_xboole_0(X4,X5) ) ),
    inference(superposition,[],[f69,f66])).

fof(f69,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f482,plain,
    ( r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))
    | ~ spl6_38 ),
    inference(avatar_component_clause,[],[f481])).

fof(f1355,plain,
    ( ~ spl6_3
    | ~ spl6_20
    | ~ spl6_21
    | spl6_38 ),
    inference(avatar_split_clause,[],[f495,f481,f199,f191,f86])).

fof(f86,plain,
    ( spl6_3
  <=> r1_tsep_1(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f191,plain,
    ( spl6_20
  <=> l1_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f199,plain,
    ( spl6_21
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f495,plain,
    ( ~ r1_tsep_1(sK5,sK4)
    | ~ spl6_20
    | ~ spl6_21
    | spl6_38 ),
    inference(unit_resulting_resolution,[],[f201,f193,f483,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( r1_tsep_1(X0,X1)
              | ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
            & ( r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
              | ~ r1_tsep_1(X0,X1) ) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f483,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK4))
    | spl6_38 ),
    inference(avatar_component_clause,[],[f481])).

fof(f193,plain,
    ( l1_struct_0(sK4)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f191])).

fof(f201,plain,
    ( l1_struct_0(sK5)
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f199])).

fof(f827,plain,
    ( ~ spl6_80
    | ~ spl6_21
    | ~ spl6_25
    | spl6_26 ),
    inference(avatar_split_clause,[],[f814,f301,f297,f199,f824])).

fof(f297,plain,
    ( spl6_25
  <=> l1_struct_0(k2_tsep_1(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f814,plain,
    ( ~ r1_xboole_0(u1_struct_0(k2_tsep_1(sK2,sK3,sK4)),u1_struct_0(sK5))
    | ~ spl6_21
    | ~ spl6_25
    | spl6_26 ),
    inference(unit_resulting_resolution,[],[f201,f303,f298,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f298,plain,
    ( l1_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f297])).

fof(f303,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK2,sK3,sK4),sK5)
    | spl6_26 ),
    inference(avatar_component_clause,[],[f301])).

fof(f813,plain,
    ( spl6_78
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f802,f353,f810])).

fof(f353,plain,
    ( spl6_32
  <=> sP1(sK2,sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f802,plain,
    ( v1_pre_topc(k2_tsep_1(sK2,sK3,sK4))
    | ~ spl6_32 ),
    inference(unit_resulting_resolution,[],[f354,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X2,X1))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X0)
        & v1_pre_topc(k2_tsep_1(X0,X2,X1))
        & ~ v2_struct_0(k2_tsep_1(X0,X2,X1)) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f42])).

fof(f42,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f354,plain,
    ( sP1(sK2,sK4,sK3)
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f353])).

fof(f808,plain,
    ( ~ spl6_77
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f803,f353,f805])).

fof(f803,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | ~ spl6_32 ),
    inference(unit_resulting_resolution,[],[f354,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X2,X1))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f608,plain,
    ( spl6_32
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | spl6_14 ),
    inference(avatar_split_clause,[],[f574,f141,f131,f126,f121,f116,f111,f353])).

fof(f574,plain,
    ( sP1(sK2,sK4,sK3)
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_11
    | ~ spl6_12
    | spl6_14 ),
    inference(unit_resulting_resolution,[],[f143,f133,f128,f123,f118,f113,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f27,f30])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f425,plain,
    ( spl6_36
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f413,f409,f422])).

fof(f413,plain,
    ( k1_xboole_0 = k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5))
    | ~ spl6_34 ),
    inference(unit_resulting_resolution,[],[f411,f213])).

fof(f411,plain,
    ( r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f409])).

fof(f412,plain,
    ( spl6_34
    | ~ spl6_2
    | ~ spl6_19
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f399,f199,f183,f82,f409])).

fof(f82,plain,
    ( spl6_2
  <=> r1_tsep_1(sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f183,plain,
    ( spl6_19
  <=> l1_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_19])])).

fof(f399,plain,
    ( r1_xboole_0(u1_struct_0(sK5),u1_struct_0(sK3))
    | ~ spl6_2
    | ~ spl6_19
    | ~ spl6_21 ),
    inference(unit_resulting_resolution,[],[f201,f185,f84,f59])).

fof(f84,plain,
    ( r1_tsep_1(sK5,sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f185,plain,
    ( l1_struct_0(sK3)
    | ~ spl6_19 ),
    inference(avatar_component_clause,[],[f183])).

fof(f407,plain,
    ( spl6_33
    | ~ spl6_19
    | ~ spl6_21
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f400,f285,f199,f183,f404])).

fof(f400,plain,
    ( r1_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5))
    | ~ spl6_19
    | ~ spl6_21
    | ~ spl6_24 ),
    inference(unit_resulting_resolution,[],[f185,f201,f287,f59])).

fof(f287,plain,
    ( r1_tsep_1(sK3,sK5)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f285])).

fof(f357,plain,
    ( ~ spl6_32
    | spl6_31 ),
    inference(avatar_split_clause,[],[f351,f344,f353])).

fof(f351,plain,
    ( ~ sP1(sK2,sK4,sK3)
    | spl6_31 ),
    inference(resolution,[],[f346,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f346,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2)
    | spl6_31 ),
    inference(avatar_component_clause,[],[f344])).

fof(f347,plain,
    ( ~ spl6_31
    | ~ spl6_12
    | spl6_27 ),
    inference(avatar_split_clause,[],[f324,f320,f131,f344])).

fof(f320,plain,
    ( spl6_27
  <=> l1_pre_topc(k2_tsep_1(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f324,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK2,sK3,sK4),sK2)
    | ~ spl6_12
    | spl6_27 ),
    inference(unit_resulting_resolution,[],[f133,f322,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f322,plain,
    ( ~ l1_pre_topc(k2_tsep_1(sK2,sK3,sK4))
    | spl6_27 ),
    inference(avatar_component_clause,[],[f320])).

fof(f323,plain,
    ( ~ spl6_27
    | spl6_25 ),
    inference(avatar_split_clause,[],[f318,f297,f320])).

fof(f318,plain,
    ( ~ l1_pre_topc(k2_tsep_1(sK2,sK3,sK4))
    | spl6_25 ),
    inference(unit_resulting_resolution,[],[f299,f61])).

fof(f61,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f299,plain,
    ( ~ l1_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | spl6_25 ),
    inference(avatar_component_clause,[],[f297])).

fof(f304,plain,
    ( ~ spl6_25
    | ~ spl6_26
    | spl6_4
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f295,f199,f91,f301,f297])).

fof(f91,plain,
    ( spl6_4
  <=> r1_tsep_1(sK5,k2_tsep_1(sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f295,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK2,sK3,sK4),sK5)
    | ~ l1_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | spl6_4
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f273,f201])).

fof(f273,plain,
    ( ~ r1_tsep_1(k2_tsep_1(sK2,sK3,sK4),sK5)
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(k2_tsep_1(sK2,sK3,sK4))
    | spl6_4 ),
    inference(resolution,[],[f68,f93])).

fof(f93,plain,
    ( ~ r1_tsep_1(sK5,k2_tsep_1(sK2,sK3,sK4))
    | spl6_4 ),
    inference(avatar_component_clause,[],[f91])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f291,plain,
    ( ~ spl6_23
    | spl6_3
    | ~ spl6_20
    | ~ spl6_21 ),
    inference(avatar_split_clause,[],[f290,f199,f191,f86,f280])).

fof(f290,plain,
    ( ~ r1_tsep_1(sK4,sK5)
    | spl6_3
    | ~ spl6_20
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f289,f193])).

fof(f289,plain,
    ( ~ r1_tsep_1(sK4,sK5)
    | ~ l1_struct_0(sK4)
    | spl6_3
    | ~ spl6_21 ),
    inference(subsumption_resolution,[],[f271,f201])).

fof(f271,plain,
    ( ~ r1_tsep_1(sK4,sK5)
    | ~ l1_struct_0(sK5)
    | ~ l1_struct_0(sK4)
    | spl6_3 ),
    inference(resolution,[],[f68,f87])).

fof(f87,plain,
    ( ~ r1_tsep_1(sK5,sK4)
    | spl6_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f203,plain,
    ( spl6_21
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f197,f170,f199])).

fof(f170,plain,
    ( spl6_18
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f197,plain,
    ( l1_struct_0(sK5)
    | ~ spl6_18 ),
    inference(resolution,[],[f172,f61])).

fof(f172,plain,
    ( l1_pre_topc(sK5)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f170])).

fof(f195,plain,
    ( spl6_20
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f189,f165,f191])).

fof(f165,plain,
    ( spl6_17
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f189,plain,
    ( l1_struct_0(sK4)
    | ~ spl6_17 ),
    inference(resolution,[],[f167,f61])).

fof(f167,plain,
    ( l1_pre_topc(sK4)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f165])).

fof(f187,plain,
    ( spl6_19
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f181,f160,f183])).

fof(f160,plain,
    ( spl6_16
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f181,plain,
    ( l1_struct_0(sK3)
    | ~ spl6_16 ),
    inference(resolution,[],[f162,f61])).

fof(f162,plain,
    ( l1_pre_topc(sK3)
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f160])).

fof(f179,plain,
    ( spl6_16
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f178,f131,f121,f160])).

fof(f178,plain,
    ( l1_pre_topc(sK3)
    | ~ spl6_10
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f158,f133])).

fof(f158,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK2)
    | ~ spl6_10 ),
    inference(resolution,[],[f62,f123])).

fof(f177,plain,
    ( spl6_17
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f176,f131,f111,f165])).

fof(f176,plain,
    ( l1_pre_topc(sK4)
    | ~ spl6_8
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f157,f133])).

fof(f157,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ spl6_8 ),
    inference(resolution,[],[f62,f113])).

fof(f175,plain,
    ( spl6_18
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f174,f131,f101,f170])).

fof(f101,plain,
    ( spl6_6
  <=> m1_pre_topc(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f174,plain,
    ( l1_pre_topc(sK5)
    | ~ spl6_6
    | ~ spl6_12 ),
    inference(subsumption_resolution,[],[f156,f133])).

fof(f156,plain,
    ( l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK2)
    | ~ spl6_6 ),
    inference(resolution,[],[f62,f103])).

fof(f103,plain,
    ( m1_pre_topc(sK5,sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f101])).

fof(f144,plain,(
    ~ spl6_14 ),
    inference(avatar_split_clause,[],[f46,f141])).

fof(f46,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( ( ( r1_tsep_1(sK5,sK4)
          | r1_tsep_1(sK5,sK3) )
        & ~ r1_tsep_1(sK5,k2_tsep_1(sK2,sK3,sK4)) )
      | sP0(sK5,sK4,sK3,sK2) )
    & ~ r1_tsep_1(sK3,sK4)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f29,f37,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( ( ( r1_tsep_1(X3,X2)
                          | r1_tsep_1(X3,X1) )
                        & ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                      | sP0(X3,X2,X1,X0) )
                    & ~ r1_tsep_1(X1,X2)
                    & m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                & m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
            & m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) )
                      & ~ r1_tsep_1(X3,k2_tsep_1(sK2,X1,X2)) )
                    | sP0(X3,X2,X1,sK2) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,sK2)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK2)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK2)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK2)
      & v2_pre_topc(sK2)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( ( ( r1_tsep_1(X3,X2)
                      | r1_tsep_1(X3,X1) )
                    & ~ r1_tsep_1(X3,k2_tsep_1(sK2,X1,X2)) )
                  | sP0(X3,X2,X1,sK2) )
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK2)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK2)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( ( ( r1_tsep_1(X3,X2)
                    | r1_tsep_1(X3,sK3) )
                  & ~ r1_tsep_1(X3,k2_tsep_1(sK2,sK3,X2)) )
                | sP0(X3,X2,sK3,sK2) )
              & ~ r1_tsep_1(sK3,X2)
              & m1_pre_topc(X3,sK2)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK2)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK3,sK2)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( ( ( r1_tsep_1(X3,X2)
                  | r1_tsep_1(X3,sK3) )
                & ~ r1_tsep_1(X3,k2_tsep_1(sK2,sK3,X2)) )
              | sP0(X3,X2,sK3,sK2) )
            & ~ r1_tsep_1(sK3,X2)
            & m1_pre_topc(X3,sK2)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( ( ( r1_tsep_1(X3,sK4)
                | r1_tsep_1(X3,sK3) )
              & ~ r1_tsep_1(X3,k2_tsep_1(sK2,sK3,sK4)) )
            | sP0(X3,sK4,sK3,sK2) )
          & ~ r1_tsep_1(sK3,sK4)
          & m1_pre_topc(X3,sK2)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK4,sK2)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X3] :
        ( ( ( ( r1_tsep_1(X3,sK4)
              | r1_tsep_1(X3,sK3) )
            & ~ r1_tsep_1(X3,k2_tsep_1(sK2,sK3,sK4)) )
          | sP0(X3,sK4,sK3,sK2) )
        & ~ r1_tsep_1(sK3,sK4)
        & m1_pre_topc(X3,sK2)
        & ~ v2_struct_0(X3) )
   => ( ( ( ( r1_tsep_1(sK5,sK4)
            | r1_tsep_1(sK5,sK3) )
          & ~ r1_tsep_1(sK5,k2_tsep_1(sK2,sK3,sK4)) )
        | sP0(sK5,sK4,sK3,sK2) )
      & ~ r1_tsep_1(sK3,sK4)
      & m1_pre_topc(sK5,sK2)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) )
                      & ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                    | sP0(X3,X2,X1,X0) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f17,f28])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) )
                      & ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                    | ( ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) )
                      & ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ( r1_tsep_1(X3,X2)
                        | r1_tsep_1(X3,X1) )
                      & ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2)) )
                    | ( ( r1_tsep_1(X2,X3)
                        | r1_tsep_1(X1,X3) )
                      & ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3) ) )
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_pre_topc(X2,X0)
                  & ~ v2_struct_0(X2) )
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & ~ v2_struct_0(X3) )
                   => ( ~ r1_tsep_1(X1,X2)
                     => ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                         => ( ~ r1_tsep_1(X3,X2)
                            & ~ r1_tsep_1(X3,X1) ) )
                        & ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                         => ( ~ r1_tsep_1(X2,X3)
                            & ~ r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & ~ v2_struct_0(X3) )
                 => ( ~ r1_tsep_1(X1,X2)
                   => ( ( ~ r1_tsep_1(X3,k2_tsep_1(X0,X1,X2))
                       => ( ~ r1_tsep_1(X3,X2)
                          & ~ r1_tsep_1(X3,X1) ) )
                      & ( ~ r1_tsep_1(k2_tsep_1(X0,X1,X2),X3)
                       => ( ~ r1_tsep_1(X2,X3)
                          & ~ r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tmap_1)).

fof(f134,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f48,f131])).

fof(f48,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f129,plain,(
    ~ spl6_11 ),
    inference(avatar_split_clause,[],[f49,f126])).

fof(f49,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f38])).

fof(f124,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f50,f121])).

fof(f50,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f119,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f51,f116])).

fof(f51,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f114,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f52,f111])).

fof(f52,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f104,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f54,f101])).

fof(f54,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f99,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f55,f96])).

fof(f55,plain,(
    ~ r1_tsep_1(sK3,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f94,plain,
    ( spl6_1
    | ~ spl6_4 ),
    inference(avatar_split_clause,[],[f56,f91,f78])).

fof(f56,plain,
    ( ~ r1_tsep_1(sK5,k2_tsep_1(sK2,sK3,sK4))
    | sP0(sK5,sK4,sK3,sK2) ),
    inference(cnf_transformation,[],[f38])).

fof(f89,plain,
    ( spl6_1
    | spl6_2
    | spl6_3 ),
    inference(avatar_split_clause,[],[f57,f86,f82,f78])).

fof(f57,plain,
    ( r1_tsep_1(sK5,sK4)
    | r1_tsep_1(sK5,sK3)
    | sP0(sK5,sK4,sK3,sK2) ),
    inference(cnf_transformation,[],[f38])).

%------------------------------------------------------------------------------
