%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:08 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  239 ( 653 expanded)
%              Number of leaves         :   49 ( 314 expanded)
%              Depth                    :    8
%              Number of atoms          :  909 (3427 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :   16 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1097,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f97,f102,f107,f117,f122,f127,f132,f137,f147,f176,f178,f180,f186,f192,f198,f215,f217,f219,f234,f277,f282,f327,f433,f438,f443,f448,f602,f652,f660,f662,f957,f960,f964,f966,f968,f972,f1027,f1028,f1031,f1069,f1093,f1094,f1095,f1096])).

fof(f1096,plain,
    ( spl8_4
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_24 ),
    inference(avatar_split_clause,[],[f1042,f231,f195,f189,f90])).

fof(f90,plain,
    ( spl8_4
  <=> r1_tsep_1(sK7,sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).

fof(f189,plain,
    ( spl8_21
  <=> l1_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).

fof(f195,plain,
    ( spl8_22
  <=> l1_struct_0(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).

fof(f231,plain,
    ( spl8_24
  <=> r1_tsep_1(sK6,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).

fof(f1042,plain,
    ( r1_tsep_1(sK7,sK6)
    | ~ spl8_21
    | ~ spl8_22
    | ~ spl8_24 ),
    inference(unit_resulting_resolution,[],[f191,f197,f233,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( r1_tsep_1(X1,X0)
      | ~ r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( l1_struct_0(X1)
        & l1_struct_0(X0) )
     => ( r1_tsep_1(X0,X1)
       => r1_tsep_1(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).

fof(f233,plain,
    ( r1_tsep_1(sK6,sK7)
    | ~ spl8_24 ),
    inference(avatar_component_clause,[],[f231])).

fof(f197,plain,
    ( l1_struct_0(sK7)
    | ~ spl8_22 ),
    inference(avatar_component_clause,[],[f195])).

fof(f191,plain,
    ( l1_struct_0(sK6)
    | ~ spl8_21 ),
    inference(avatar_component_clause,[],[f189])).

fof(f1095,plain,
    ( spl8_28
    | ~ spl8_3
    | ~ spl8_20
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f983,f195,f183,f86,f279])).

fof(f279,plain,
    ( spl8_28
  <=> r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).

fof(f86,plain,
    ( spl8_3
  <=> r1_tsep_1(sK7,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).

fof(f183,plain,
    ( spl8_20
  <=> l1_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).

fof(f983,plain,
    ( r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5))
    | ~ spl8_3
    | ~ spl8_20
    | ~ spl8_22 ),
    inference(unit_resulting_resolution,[],[f197,f185,f87,f62])).

fof(f62,plain,(
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
    inference(nnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ( r1_tsep_1(X0,X1)
          <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).

fof(f87,plain,
    ( r1_tsep_1(sK7,sK5)
    | ~ spl8_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f185,plain,
    ( l1_struct_0(sK5)
    | ~ spl8_20 ),
    inference(avatar_component_clause,[],[f183])).

fof(f1094,plain,
    ( spl8_27
    | ~ spl8_4
    | ~ spl8_21
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f1033,f195,f189,f90,f274])).

fof(f274,plain,
    ( spl8_27
  <=> r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).

fof(f1033,plain,
    ( r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ spl8_4
    | ~ spl8_21
    | ~ spl8_22 ),
    inference(unit_resulting_resolution,[],[f197,f191,f91,f62])).

fof(f91,plain,
    ( r1_tsep_1(sK7,sK6)
    | ~ spl8_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f1093,plain,
    ( ~ spl8_27
    | ~ spl8_28
    | spl8_129 ),
    inference(avatar_contradiction_clause,[],[f1092])).

fof(f1092,plain,
    ( $false
    | ~ spl8_27
    | ~ spl8_28
    | spl8_129 ),
    inference(subsumption_resolution,[],[f1084,f979])).

fof(f979,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6)))
    | spl8_129 ),
    inference(avatar_component_clause,[],[f978])).

fof(f978,plain,
    ( spl8_129
  <=> r1_xboole_0(u1_struct_0(sK7),k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_129])])).

fof(f1084,plain,
    ( r1_xboole_0(u1_struct_0(sK7),k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6)))
    | ~ spl8_27
    | ~ spl8_28 ),
    inference(unit_resulting_resolution,[],[f275,f280,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | ~ r1_xboole_0(X0,X1)
      | ~ r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
        | ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1) ) )
      & ( ~ r1_xboole_0(X0,X2)
        | ~ r1_xboole_0(X0,X1)
        | r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( ~ ( r1_xboole_0(X0,k2_xboole_0(X1,X2))
          & ~ ( r1_xboole_0(X0,X2)
              & r1_xboole_0(X0,X1) ) )
      & ~ ( r1_xboole_0(X0,X2)
          & r1_xboole_0(X0,X1)
          & ~ r1_xboole_0(X0,k2_xboole_0(X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

fof(f280,plain,
    ( r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5))
    | ~ spl8_28 ),
    inference(avatar_component_clause,[],[f279])).

fof(f275,plain,
    ( r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))
    | ~ spl8_27 ),
    inference(avatar_component_clause,[],[f274])).

fof(f1069,plain,
    ( ~ spl8_129
    | spl8_6
    | ~ spl8_22
    | ~ spl8_77
    | ~ spl8_128 ),
    inference(avatar_split_clause,[],[f1066,f954,f599,f195,f99,f978])).

fof(f99,plain,
    ( spl8_6
  <=> r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).

fof(f599,plain,
    ( spl8_77
  <=> l1_struct_0(k1_tsep_1(sK4,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_77])])).

fof(f954,plain,
    ( spl8_128
  <=> u1_struct_0(k1_tsep_1(sK4,sK5,sK6)) = k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_128])])).

fof(f1066,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6)))
    | spl8_6
    | ~ spl8_22
    | ~ spl8_77
    | ~ spl8_128 ),
    inference(forward_demodulation,[],[f1059,f956])).

fof(f956,plain,
    ( u1_struct_0(k1_tsep_1(sK4,sK5,sK6)) = k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ spl8_128 ),
    inference(avatar_component_clause,[],[f954])).

fof(f1059,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(k1_tsep_1(sK4,sK5,sK6)))
    | spl8_6
    | ~ spl8_22
    | ~ spl8_77 ),
    inference(unit_resulting_resolution,[],[f197,f601,f100,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))
      | r1_tsep_1(X0,X1)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f100,plain,
    ( ~ r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6))
    | spl8_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f601,plain,
    ( l1_struct_0(k1_tsep_1(sK4,sK5,sK6))
    | ~ spl8_77 ),
    inference(avatar_component_clause,[],[f599])).

fof(f1031,plain,
    ( ~ spl8_24
    | ~ spl8_1
    | ~ spl8_23 ),
    inference(avatar_split_clause,[],[f1030,f211,f78,f231])).

fof(f78,plain,
    ( spl8_1
  <=> sP2(sK7,sK6,sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).

fof(f211,plain,
    ( spl8_23
  <=> r1_tsep_1(sK5,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).

fof(f1030,plain,
    ( ~ r1_tsep_1(sK6,sK7)
    | ~ spl8_1
    | ~ spl8_23 ),
    inference(subsumption_resolution,[],[f997,f213])).

fof(f213,plain,
    ( r1_tsep_1(sK5,sK7)
    | ~ spl8_23 ),
    inference(avatar_component_clause,[],[f211])).

fof(f997,plain,
    ( ~ r1_tsep_1(sK5,sK7)
    | ~ r1_tsep_1(sK6,sK7)
    | ~ spl8_1 ),
    inference(resolution,[],[f80,f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP2(X0,X1,X2,X3)
      | ~ r1_tsep_1(X2,X0)
      | ~ r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( ~ r1_tsep_1(X1,X0)
          | ~ r1_tsep_1(X2,X0) )
        & r1_tsep_1(k1_tsep_1(X3,X2,X1),X0) )
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f28])).

fof(f28,plain,(
    ! [X3,X2,X1,X0] :
      ( ( ( ~ r1_tsep_1(X2,X3)
          | ~ r1_tsep_1(X1,X3) )
        & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) )
      | ~ sP2(X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X3,X2,X1,X0] :
      ( ( ( ~ r1_tsep_1(X2,X3)
          | ~ r1_tsep_1(X1,X3) )
        & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) )
      | ~ sP2(X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).

fof(f80,plain,
    ( sP2(sK7,sK6,sK5,sK4)
    | ~ spl8_1 ),
    inference(avatar_component_clause,[],[f78])).

fof(f1028,plain,
    ( spl8_83
    | ~ spl8_1 ),
    inference(avatar_split_clause,[],[f995,f78,f644])).

fof(f644,plain,
    ( spl8_83
  <=> r1_tsep_1(k1_tsep_1(sK4,sK5,sK6),sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_83])])).

fof(f995,plain,
    ( r1_tsep_1(k1_tsep_1(sK4,sK5,sK6),sK7)
    | ~ spl8_1 ),
    inference(unit_resulting_resolution,[],[f80,f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tsep_1(k1_tsep_1(X3,X2,X1),X0)
      | ~ sP2(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1027,plain,
    ( ~ spl8_83
    | spl8_6
    | ~ spl8_22
    | ~ spl8_77 ),
    inference(avatar_split_clause,[],[f1011,f599,f195,f99,f644])).

fof(f1011,plain,
    ( ~ r1_tsep_1(k1_tsep_1(sK4,sK5,sK6),sK7)
    | spl8_6
    | ~ spl8_22
    | ~ spl8_77 ),
    inference(unit_resulting_resolution,[],[f197,f601,f100,f68])).

fof(f972,plain,
    ( ~ spl8_2
    | ~ spl8_6
    | ~ spl8_22
    | ~ spl8_77 ),
    inference(avatar_split_clause,[],[f670,f599,f195,f99,f82])).

fof(f82,plain,
    ( spl8_2
  <=> sP0(sK7,sK6,sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).

fof(f670,plain,
    ( ~ sP0(sK7,sK6,sK5,sK4)
    | ~ spl8_6
    | ~ spl8_22
    | ~ spl8_77 ),
    inference(unit_resulting_resolution,[],[f197,f601,f101,f254])).

fof(f254,plain,(
    ! [X6,X4,X7,X5] :
      ( ~ r1_tsep_1(X4,k1_tsep_1(X7,X6,X5))
      | ~ sP0(X4,X5,X6,X7)
      | ~ l1_struct_0(k1_tsep_1(X7,X6,X5))
      | ~ l1_struct_0(X4) ) ),
    inference(resolution,[],[f50,f68])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(k1_tsep_1(X3,X2,X1),X0)
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ~ r1_tsep_1(k1_tsep_1(X3,X2,X1),X0)
        & r1_tsep_1(X1,X0)
        & r1_tsep_1(X2,X0) )
      | ~ sP0(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f32])).

fof(f32,plain,(
    ! [X3,X2,X1,X0] :
      ( ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
        & r1_tsep_1(X2,X3)
        & r1_tsep_1(X1,X3) )
      | ~ sP0(X3,X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X3,X2,X1,X0] :
      ( ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
        & r1_tsep_1(X2,X3)
        & r1_tsep_1(X1,X3) )
      | ~ sP0(X3,X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f101,plain,
    ( r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6))
    | ~ spl8_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f968,plain,
    ( ~ spl8_5
    | ~ spl8_6 ),
    inference(avatar_split_clause,[],[f671,f99,f94])).

fof(f94,plain,
    ( spl8_5
  <=> sP1(sK6,sK5,sK4,sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).

fof(f671,plain,
    ( ~ sP1(sK6,sK5,sK4,sK7)
    | ~ spl8_6 ),
    inference(unit_resulting_resolution,[],[f101,f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r1_tsep_1(X3,k1_tsep_1(X2,X1,X0))
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ~ r1_tsep_1(X3,k1_tsep_1(X2,X1,X0))
        & r1_tsep_1(X3,X0)
        & r1_tsep_1(X3,X1) )
      | ~ sP1(X0,X1,X2,X3) ) ),
    inference(rectify,[],[f30])).

fof(f30,plain,(
    ! [X2,X1,X0,X3] :
      ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
        & r1_tsep_1(X3,X2)
        & r1_tsep_1(X3,X1) )
      | ~ sP1(X2,X1,X0,X3) ) ),
    inference(nnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X2,X1,X0,X3] :
      ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
        & r1_tsep_1(X3,X2)
        & r1_tsep_1(X3,X1) )
      | ~ sP1(X2,X1,X0,X3) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f966,plain,
    ( spl8_27
    | ~ spl8_84
    | ~ spl8_128 ),
    inference(avatar_contradiction_clause,[],[f965])).

fof(f965,plain,
    ( $false
    | spl8_27
    | ~ spl8_84
    | ~ spl8_128 ),
    inference(subsumption_resolution,[],[f958,f288])).

fof(f288,plain,
    ( ! [X0] : ~ r1_xboole_0(u1_struct_0(sK7),k2_xboole_0(X0,u1_struct_0(sK6)))
    | spl8_27 ),
    inference(unit_resulting_resolution,[],[f276,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f276,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))
    | spl8_27 ),
    inference(avatar_component_clause,[],[f274])).

fof(f958,plain,
    ( r1_xboole_0(u1_struct_0(sK7),k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6)))
    | ~ spl8_84
    | ~ spl8_128 ),
    inference(backward_demodulation,[],[f651,f956])).

fof(f651,plain,
    ( r1_xboole_0(u1_struct_0(sK7),u1_struct_0(k1_tsep_1(sK4,sK5,sK6)))
    | ~ spl8_84 ),
    inference(avatar_component_clause,[],[f649])).

fof(f649,plain,
    ( spl8_84
  <=> r1_xboole_0(u1_struct_0(sK7),u1_struct_0(k1_tsep_1(sK4,sK5,sK6))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_84])])).

fof(f964,plain,
    ( ~ spl8_3
    | ~ spl8_20
    | ~ spl8_22
    | spl8_23 ),
    inference(avatar_split_clause,[],[f664,f211,f195,f183,f86])).

fof(f664,plain,
    ( ~ r1_tsep_1(sK7,sK5)
    | ~ spl8_20
    | ~ spl8_22
    | spl8_23 ),
    inference(unit_resulting_resolution,[],[f197,f185,f212,f68])).

fof(f212,plain,
    ( ~ r1_tsep_1(sK5,sK7)
    | spl8_23 ),
    inference(avatar_component_clause,[],[f211])).

fof(f960,plain,
    ( spl8_28
    | ~ spl8_84
    | ~ spl8_128 ),
    inference(avatar_contradiction_clause,[],[f959])).

fof(f959,plain,
    ( $false
    | spl8_28
    | ~ spl8_84
    | ~ spl8_128 ),
    inference(subsumption_resolution,[],[f958,f293])).

fof(f293,plain,
    ( ! [X0] : ~ r1_xboole_0(u1_struct_0(sK7),k2_xboole_0(u1_struct_0(sK5),X0))
    | spl8_28 ),
    inference(unit_resulting_resolution,[],[f281,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_xboole_0(X0,k2_xboole_0(X1,X2))
      | r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f281,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5))
    | spl8_28 ),
    inference(avatar_component_clause,[],[f279])).

fof(f957,plain,
    ( spl8_128
    | ~ spl8_9
    | spl8_10
    | ~ spl8_11
    | spl8_12
    | ~ spl8_13
    | spl8_15
    | spl8_50
    | ~ spl8_51
    | ~ spl8_52 ),
    inference(avatar_split_clause,[],[f870,f440,f435,f430,f144,f134,f129,f124,f119,f114,f954])).

fof(f114,plain,
    ( spl8_9
  <=> m1_pre_topc(sK6,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).

fof(f119,plain,
    ( spl8_10
  <=> v2_struct_0(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).

fof(f124,plain,
    ( spl8_11
  <=> m1_pre_topc(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).

fof(f129,plain,
    ( spl8_12
  <=> v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).

fof(f134,plain,
    ( spl8_13
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).

fof(f144,plain,
    ( spl8_15
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).

fof(f430,plain,
    ( spl8_50
  <=> v2_struct_0(k1_tsep_1(sK4,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).

fof(f435,plain,
    ( spl8_51
  <=> v1_pre_topc(k1_tsep_1(sK4,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).

fof(f440,plain,
    ( spl8_52
  <=> m1_pre_topc(k1_tsep_1(sK4,sK5,sK6),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).

fof(f870,plain,
    ( u1_struct_0(k1_tsep_1(sK4,sK5,sK6)) = k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6))
    | ~ spl8_9
    | spl8_10
    | ~ spl8_11
    | spl8_12
    | ~ spl8_13
    | spl8_15
    | spl8_50
    | ~ spl8_51
    | ~ spl8_52 ),
    inference(unit_resulting_resolution,[],[f146,f136,f131,f121,f126,f116,f432,f437,f442,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X2,X0,X3,X1] :
      ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k1_tsep_1(X0,X1,X2) != X3
      | ~ m1_pre_topc(X3,X0)
      | ~ v1_pre_topc(X3)
      | v2_struct_0(X3)
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
                  ( ( ( k1_tsep_1(X0,X1,X2) = X3
                      | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                    & ( u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
                      | k1_tsep_1(X0,X1,X2) != X3 ) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) )
                  | ~ m1_pre_topc(X3,X0)
                  | ~ v1_pre_topc(X3)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).

fof(f442,plain,
    ( m1_pre_topc(k1_tsep_1(sK4,sK5,sK6),sK4)
    | ~ spl8_52 ),
    inference(avatar_component_clause,[],[f440])).

fof(f437,plain,
    ( v1_pre_topc(k1_tsep_1(sK4,sK5,sK6))
    | ~ spl8_51 ),
    inference(avatar_component_clause,[],[f435])).

fof(f432,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK4,sK5,sK6))
    | spl8_50 ),
    inference(avatar_component_clause,[],[f430])).

fof(f116,plain,
    ( m1_pre_topc(sK6,sK4)
    | ~ spl8_9 ),
    inference(avatar_component_clause,[],[f114])).

fof(f126,plain,
    ( m1_pre_topc(sK5,sK4)
    | ~ spl8_11 ),
    inference(avatar_component_clause,[],[f124])).

fof(f121,plain,
    ( ~ v2_struct_0(sK6)
    | spl8_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f131,plain,
    ( ~ v2_struct_0(sK5)
    | spl8_12 ),
    inference(avatar_component_clause,[],[f129])).

fof(f136,plain,
    ( l1_pre_topc(sK4)
    | ~ spl8_13 ),
    inference(avatar_component_clause,[],[f134])).

fof(f146,plain,
    ( ~ v2_struct_0(sK4)
    | spl8_15 ),
    inference(avatar_component_clause,[],[f144])).

fof(f662,plain,
    ( ~ spl8_2
    | spl8_24 ),
    inference(avatar_contradiction_clause,[],[f661])).

fof(f661,plain,
    ( $false
    | ~ spl8_2
    | spl8_24 ),
    inference(subsumption_resolution,[],[f84,f243])).

fof(f243,plain,
    ( ! [X0,X1] : ~ sP0(sK7,sK6,X0,X1)
    | spl8_24 ),
    inference(unit_resulting_resolution,[],[f232,f49])).

fof(f49,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f232,plain,
    ( ~ r1_tsep_1(sK6,sK7)
    | spl8_24 ),
    inference(avatar_component_clause,[],[f231])).

fof(f84,plain,
    ( sP0(sK7,sK6,sK5,sK4)
    | ~ spl8_2 ),
    inference(avatar_component_clause,[],[f82])).

fof(f660,plain,
    ( ~ spl8_23
    | spl8_3
    | ~ spl8_20
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f226,f195,f183,f86,f211])).

fof(f226,plain,
    ( ~ r1_tsep_1(sK5,sK7)
    | spl8_3
    | ~ spl8_20
    | ~ spl8_22 ),
    inference(unit_resulting_resolution,[],[f185,f197,f88,f68])).

fof(f88,plain,
    ( ~ r1_tsep_1(sK7,sK5)
    | spl8_3 ),
    inference(avatar_component_clause,[],[f86])).

fof(f652,plain,
    ( spl8_84
    | ~ spl8_6
    | ~ spl8_22
    | ~ spl8_77 ),
    inference(avatar_split_clause,[],[f641,f599,f195,f99,f649])).

fof(f641,plain,
    ( r1_xboole_0(u1_struct_0(sK7),u1_struct_0(k1_tsep_1(sK4,sK5,sK6)))
    | ~ spl8_6
    | ~ spl8_22
    | ~ spl8_77 ),
    inference(unit_resulting_resolution,[],[f197,f101,f601,f62])).

fof(f602,plain,
    ( spl8_77
    | ~ spl8_53 ),
    inference(avatar_split_clause,[],[f597,f445,f599])).

fof(f445,plain,
    ( spl8_53
  <=> l1_pre_topc(k1_tsep_1(sK4,sK5,sK6)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).

fof(f597,plain,
    ( l1_struct_0(k1_tsep_1(sK4,sK5,sK6))
    | ~ spl8_53 ),
    inference(unit_resulting_resolution,[],[f447,f64])).

fof(f64,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f447,plain,
    ( l1_pre_topc(k1_tsep_1(sK4,sK5,sK6))
    | ~ spl8_53 ),
    inference(avatar_component_clause,[],[f445])).

fof(f448,plain,
    ( spl8_53
    | ~ spl8_13
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f425,f324,f134,f445])).

fof(f324,plain,
    ( spl8_32
  <=> sP3(sK4,sK6,sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).

fof(f425,plain,
    ( l1_pre_topc(k1_tsep_1(sK4,sK5,sK6))
    | ~ spl8_13
    | ~ spl8_32 ),
    inference(unit_resulting_resolution,[],[f136,f326,f241])).

fof(f241,plain,(
    ! [X2,X0,X1] :
      ( l1_pre_topc(k1_tsep_1(X0,X2,X1))
      | ~ sP3(X0,X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f74,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
        & v1_pre_topc(k1_tsep_1(X0,X2,X1))
        & ~ v2_struct_0(k1_tsep_1(X0,X2,X1)) )
      | ~ sP3(X0,X1,X2) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP3(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP3(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).

fof(f326,plain,
    ( sP3(sK4,sK6,sK5)
    | ~ spl8_32 ),
    inference(avatar_component_clause,[],[f324])).

fof(f443,plain,
    ( spl8_52
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f426,f324,f440])).

fof(f426,plain,
    ( m1_pre_topc(k1_tsep_1(sK4,sK5,sK6),sK4)
    | ~ spl8_32 ),
    inference(unit_resulting_resolution,[],[f326,f74])).

fof(f438,plain,
    ( spl8_51
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f427,f324,f435])).

fof(f427,plain,
    ( v1_pre_topc(k1_tsep_1(sK4,sK5,sK6))
    | ~ spl8_32 ),
    inference(unit_resulting_resolution,[],[f326,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X2,X1))
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f433,plain,
    ( ~ spl8_50
    | ~ spl8_32 ),
    inference(avatar_split_clause,[],[f428,f324,f430])).

fof(f428,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK4,sK5,sK6))
    | ~ spl8_32 ),
    inference(unit_resulting_resolution,[],[f326,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X2,X1))
      | ~ sP3(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f327,plain,
    ( spl8_32
    | ~ spl8_9
    | spl8_10
    | ~ spl8_11
    | spl8_12
    | ~ spl8_13
    | spl8_15 ),
    inference(avatar_split_clause,[],[f304,f144,f134,f129,f124,f119,f114,f324])).

fof(f304,plain,
    ( sP3(sK4,sK6,sK5)
    | ~ spl8_9
    | spl8_10
    | ~ spl8_11
    | spl8_12
    | ~ spl8_13
    | spl8_15 ),
    inference(unit_resulting_resolution,[],[f146,f136,f131,f126,f121,f116,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( sP3(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( sP3(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f21,f26])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f282,plain,
    ( ~ spl8_28
    | spl8_3
    | ~ spl8_20
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f257,f195,f183,f86,f279])).

fof(f257,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5))
    | spl8_3
    | ~ spl8_20
    | ~ spl8_22 ),
    inference(unit_resulting_resolution,[],[f197,f185,f88,f63])).

fof(f277,plain,
    ( ~ spl8_27
    | spl8_4
    | ~ spl8_21
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f258,f195,f189,f90,f274])).

fof(f258,plain,
    ( ~ r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))
    | spl8_4
    | ~ spl8_21
    | ~ spl8_22 ),
    inference(unit_resulting_resolution,[],[f197,f191,f92,f63])).

fof(f92,plain,
    ( ~ r1_tsep_1(sK7,sK6)
    | spl8_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f234,plain,
    ( spl8_24
    | ~ spl8_4
    | ~ spl8_21
    | ~ spl8_22 ),
    inference(avatar_split_clause,[],[f225,f195,f189,f90,f231])).

fof(f225,plain,
    ( r1_tsep_1(sK6,sK7)
    | ~ spl8_4
    | ~ spl8_21
    | ~ spl8_22 ),
    inference(unit_resulting_resolution,[],[f197,f191,f91,f68])).

fof(f219,plain,
    ( spl8_3
    | ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f218])).

fof(f218,plain,
    ( $false
    | spl8_3
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f96,f199])).

fof(f199,plain,
    ( ! [X0,X1] : ~ sP1(X0,sK5,X1,sK7)
    | spl8_3 ),
    inference(unit_resulting_resolution,[],[f88,f45])).

fof(f45,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | r1_tsep_1(X3,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f96,plain,
    ( sP1(sK6,sK5,sK4,sK7)
    | ~ spl8_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f217,plain,
    ( spl8_4
    | ~ spl8_5 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | spl8_4
    | ~ spl8_5 ),
    inference(subsumption_resolution,[],[f96,f203])).

fof(f203,plain,
    ( ! [X0,X1] : ~ sP1(sK6,X0,X1,sK7)
    | spl8_4 ),
    inference(unit_resulting_resolution,[],[f92,f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP1(X0,X1,X2,X3)
      | r1_tsep_1(X3,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f215,plain,
    ( spl8_23
    | ~ spl8_2 ),
    inference(avatar_split_clause,[],[f209,f82,f211])).

fof(f209,plain,
    ( r1_tsep_1(sK5,sK7)
    | ~ spl8_2 ),
    inference(resolution,[],[f48,f84])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP0(X0,X1,X2,X3)
      | r1_tsep_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f198,plain,
    ( spl8_22
    | ~ spl8_19 ),
    inference(avatar_split_clause,[],[f193,f171,f195])).

fof(f171,plain,
    ( spl8_19
  <=> l1_pre_topc(sK7) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).

fof(f193,plain,
    ( l1_struct_0(sK7)
    | ~ spl8_19 ),
    inference(unit_resulting_resolution,[],[f173,f64])).

fof(f173,plain,
    ( l1_pre_topc(sK7)
    | ~ spl8_19 ),
    inference(avatar_component_clause,[],[f171])).

fof(f192,plain,
    ( spl8_21
    | ~ spl8_18 ),
    inference(avatar_split_clause,[],[f187,f166,f189])).

fof(f166,plain,
    ( spl8_18
  <=> l1_pre_topc(sK6) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).

fof(f187,plain,
    ( l1_struct_0(sK6)
    | ~ spl8_18 ),
    inference(unit_resulting_resolution,[],[f168,f64])).

fof(f168,plain,
    ( l1_pre_topc(sK6)
    | ~ spl8_18 ),
    inference(avatar_component_clause,[],[f166])).

fof(f186,plain,
    ( spl8_20
    | ~ spl8_17 ),
    inference(avatar_split_clause,[],[f181,f161,f183])).

fof(f161,plain,
    ( spl8_17
  <=> l1_pre_topc(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).

fof(f181,plain,
    ( l1_struct_0(sK5)
    | ~ spl8_17 ),
    inference(unit_resulting_resolution,[],[f163,f64])).

fof(f163,plain,
    ( l1_pre_topc(sK5)
    | ~ spl8_17 ),
    inference(avatar_component_clause,[],[f161])).

fof(f180,plain,
    ( spl8_17
    | ~ spl8_11
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f179,f134,f124,f161])).

fof(f179,plain,
    ( l1_pre_topc(sK5)
    | ~ spl8_11
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f159,f136])).

fof(f159,plain,
    ( l1_pre_topc(sK5)
    | ~ l1_pre_topc(sK4)
    | ~ spl8_11 ),
    inference(resolution,[],[f65,f126])).

fof(f178,plain,
    ( spl8_18
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f177,f134,f114,f166])).

fof(f177,plain,
    ( l1_pre_topc(sK6)
    | ~ spl8_9
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f158,f136])).

fof(f158,plain,
    ( l1_pre_topc(sK6)
    | ~ l1_pre_topc(sK4)
    | ~ spl8_9 ),
    inference(resolution,[],[f65,f116])).

fof(f176,plain,
    ( spl8_19
    | ~ spl8_7
    | ~ spl8_13 ),
    inference(avatar_split_clause,[],[f175,f134,f104,f171])).

fof(f104,plain,
    ( spl8_7
  <=> m1_pre_topc(sK7,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).

fof(f175,plain,
    ( l1_pre_topc(sK7)
    | ~ spl8_7
    | ~ spl8_13 ),
    inference(subsumption_resolution,[],[f157,f136])).

fof(f157,plain,
    ( l1_pre_topc(sK7)
    | ~ l1_pre_topc(sK4)
    | ~ spl8_7 ),
    inference(resolution,[],[f65,f106])).

fof(f106,plain,
    ( m1_pre_topc(sK7,sK4)
    | ~ spl8_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f147,plain,(
    ~ spl8_15 ),
    inference(avatar_split_clause,[],[f51,f144])).

fof(f51,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,
    ( ( sP1(sK6,sK5,sK4,sK7)
      | ( ( ~ r1_tsep_1(sK7,sK6)
          | ~ r1_tsep_1(sK7,sK5) )
        & r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6)) )
      | sP0(sK7,sK6,sK5,sK4)
      | sP2(sK7,sK6,sK5,sK4) )
    & m1_pre_topc(sK7,sK4)
    & ~ v2_struct_0(sK7)
    & m1_pre_topc(sK6,sK4)
    & ~ v2_struct_0(sK6)
    & m1_pre_topc(sK5,sK4)
    & ~ v2_struct_0(sK5)
    & l1_pre_topc(sK4)
    & v2_pre_topc(sK4)
    & ~ v2_struct_0(sK4) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f25,f37,f36,f35,f34])).

fof(f34,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ( sP1(X2,X1,X0,X3)
                      | ( ( ~ r1_tsep_1(X3,X2)
                          | ~ r1_tsep_1(X3,X1) )
                        & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                      | sP0(X3,X2,X1,X0)
                      | sP2(X3,X2,X1,X0) )
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
                  ( ( sP1(X2,X1,sK4,X3)
                    | ( ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) )
                      & r1_tsep_1(X3,k1_tsep_1(sK4,X1,X2)) )
                    | sP0(X3,X2,X1,sK4)
                    | sP2(X3,X2,X1,sK4) )
                  & m1_pre_topc(X3,sK4)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK4)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK4)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK4)
      & v2_pre_topc(sK4)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f35,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ( sP1(X2,X1,sK4,X3)
                  | ( ( ~ r1_tsep_1(X3,X2)
                      | ~ r1_tsep_1(X3,X1) )
                    & r1_tsep_1(X3,k1_tsep_1(sK4,X1,X2)) )
                  | sP0(X3,X2,X1,sK4)
                  | sP2(X3,X2,X1,sK4) )
                & m1_pre_topc(X3,sK4)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK4)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK4)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ( sP1(X2,sK5,sK4,X3)
                | ( ( ~ r1_tsep_1(X3,X2)
                    | ~ r1_tsep_1(X3,sK5) )
                  & r1_tsep_1(X3,k1_tsep_1(sK4,sK5,X2)) )
                | sP0(X3,X2,sK5,sK4)
                | sP2(X3,X2,sK5,sK4) )
              & m1_pre_topc(X3,sK4)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK4)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK5,sK4)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f36,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ( sP1(X2,sK5,sK4,X3)
              | ( ( ~ r1_tsep_1(X3,X2)
                  | ~ r1_tsep_1(X3,sK5) )
                & r1_tsep_1(X3,k1_tsep_1(sK4,sK5,X2)) )
              | sP0(X3,X2,sK5,sK4)
              | sP2(X3,X2,sK5,sK4) )
            & m1_pre_topc(X3,sK4)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK4)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ( sP1(sK6,sK5,sK4,X3)
            | ( ( ~ r1_tsep_1(X3,sK6)
                | ~ r1_tsep_1(X3,sK5) )
              & r1_tsep_1(X3,k1_tsep_1(sK4,sK5,sK6)) )
            | sP0(X3,sK6,sK5,sK4)
            | sP2(X3,sK6,sK5,sK4) )
          & m1_pre_topc(X3,sK4)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK6,sK4)
      & ~ v2_struct_0(sK6) ) ),
    introduced(choice_axiom,[])).

fof(f37,plain,
    ( ? [X3] :
        ( ( sP1(sK6,sK5,sK4,X3)
          | ( ( ~ r1_tsep_1(X3,sK6)
              | ~ r1_tsep_1(X3,sK5) )
            & r1_tsep_1(X3,k1_tsep_1(sK4,sK5,sK6)) )
          | sP0(X3,sK6,sK5,sK4)
          | sP2(X3,sK6,sK5,sK4) )
        & m1_pre_topc(X3,sK4)
        & ~ v2_struct_0(X3) )
   => ( ( sP1(sK6,sK5,sK4,sK7)
        | ( ( ~ r1_tsep_1(sK7,sK6)
            | ~ r1_tsep_1(sK7,sK5) )
          & r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6)) )
        | sP0(sK7,sK6,sK5,sK4)
        | sP2(sK7,sK6,sK5,sK4) )
      & m1_pre_topc(sK7,sK4)
      & ~ v2_struct_0(sK7) ) ),
    introduced(choice_axiom,[])).

fof(f25,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( sP1(X2,X1,X0,X3)
                    | ( ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) )
                      & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | sP0(X3,X2,X1,X0)
                    | sP2(X3,X2,X1,X0) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f11,f24,f23,f22])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      & r1_tsep_1(X3,X2)
                      & r1_tsep_1(X3,X1) )
                    | ( ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) )
                      & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      & r1_tsep_1(X2,X3)
                      & r1_tsep_1(X1,X3) )
                    | ( ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) )
                      & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( ~ r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                      & r1_tsep_1(X3,X2)
                      & r1_tsep_1(X3,X1) )
                    | ( ( ~ r1_tsep_1(X3,X2)
                        | ~ r1_tsep_1(X3,X1) )
                      & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    | ( ~ r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                      & r1_tsep_1(X2,X3)
                      & r1_tsep_1(X1,X3) )
                    | ( ( ~ r1_tsep_1(X2,X3)
                        | ~ r1_tsep_1(X1,X3) )
                      & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) ) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
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
                   => ( ( ( r1_tsep_1(X3,X2)
                          & r1_tsep_1(X3,X1) )
                       => r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                      & ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                       => ( r1_tsep_1(X3,X2)
                          & r1_tsep_1(X3,X1) ) )
                      & ( ( r1_tsep_1(X2,X3)
                          & r1_tsep_1(X1,X3) )
                       => r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) )
                      & ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                       => ( r1_tsep_1(X2,X3)
                          & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
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
                 => ( ( ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1) )
                     => r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) )
                    & ( r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))
                     => ( r1_tsep_1(X3,X2)
                        & r1_tsep_1(X3,X1) ) )
                    & ( ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3) )
                     => r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) )
                    & ( r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)
                     => ( r1_tsep_1(X2,X3)
                        & r1_tsep_1(X1,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_tmap_1)).

fof(f137,plain,(
    spl8_13 ),
    inference(avatar_split_clause,[],[f53,f134])).

fof(f53,plain,(
    l1_pre_topc(sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f132,plain,(
    ~ spl8_12 ),
    inference(avatar_split_clause,[],[f54,f129])).

fof(f54,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f38])).

fof(f127,plain,(
    spl8_11 ),
    inference(avatar_split_clause,[],[f55,f124])).

fof(f55,plain,(
    m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f122,plain,(
    ~ spl8_10 ),
    inference(avatar_split_clause,[],[f56,f119])).

fof(f56,plain,(
    ~ v2_struct_0(sK6) ),
    inference(cnf_transformation,[],[f38])).

fof(f117,plain,(
    spl8_9 ),
    inference(avatar_split_clause,[],[f57,f114])).

fof(f57,plain,(
    m1_pre_topc(sK6,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f107,plain,(
    spl8_7 ),
    inference(avatar_split_clause,[],[f59,f104])).

fof(f59,plain,(
    m1_pre_topc(sK7,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f102,plain,
    ( spl8_1
    | spl8_2
    | spl8_6
    | spl8_5 ),
    inference(avatar_split_clause,[],[f60,f94,f99,f82,f78])).

fof(f60,plain,
    ( sP1(sK6,sK5,sK4,sK7)
    | r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6))
    | sP0(sK7,sK6,sK5,sK4)
    | sP2(sK7,sK6,sK5,sK4) ),
    inference(cnf_transformation,[],[f38])).

fof(f97,plain,
    ( spl8_1
    | spl8_2
    | ~ spl8_3
    | ~ spl8_4
    | spl8_5 ),
    inference(avatar_split_clause,[],[f61,f94,f90,f86,f82,f78])).

fof(f61,plain,
    ( sP1(sK6,sK5,sK4,sK7)
    | ~ r1_tsep_1(sK7,sK6)
    | ~ r1_tsep_1(sK7,sK5)
    | sP0(sK7,sK6,sK5,sK4)
    | sP2(sK7,sK6,sK5,sK4) ),
    inference(cnf_transformation,[],[f38])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n014.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 18:25:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.41  % (13938)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.47  % (13926)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (13926)Refutation not found, incomplete strategy% (13926)------------------------------
% 0.21/0.47  % (13926)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (13926)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (13926)Memory used [KB]: 10618
% 0.21/0.47  % (13926)Time elapsed: 0.055 s
% 0.21/0.47  % (13926)------------------------------
% 0.21/0.47  % (13926)------------------------------
% 0.21/0.48  % (13925)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (13933)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (13932)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (13930)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (13940)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (13931)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (13928)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (13942)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  % (13929)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (13927)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (13939)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (13943)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (13944)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (13941)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (13937)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (13934)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  % (13935)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.51  % (13945)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (13935)Refutation not found, incomplete strategy% (13935)------------------------------
% 0.21/0.52  % (13935)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13935)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13935)Memory used [KB]: 6140
% 0.21/0.52  % (13935)Time elapsed: 0.109 s
% 0.21/0.52  % (13935)------------------------------
% 0.21/0.52  % (13935)------------------------------
% 0.21/0.52  % (13945)Refutation not found, incomplete strategy% (13945)------------------------------
% 0.21/0.52  % (13945)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13945)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13945)Memory used [KB]: 10618
% 0.21/0.52  % (13945)Time elapsed: 0.107 s
% 0.21/0.52  % (13945)------------------------------
% 0.21/0.52  % (13945)------------------------------
% 0.21/0.52  % (13936)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.53  % (13941)Refutation found. Thanks to Tanya!
% 0.21/0.53  % SZS status Theorem for theBenchmark
% 0.21/0.53  % SZS output start Proof for theBenchmark
% 0.21/0.53  fof(f1097,plain,(
% 0.21/0.53    $false),
% 0.21/0.53    inference(avatar_sat_refutation,[],[f97,f102,f107,f117,f122,f127,f132,f137,f147,f176,f178,f180,f186,f192,f198,f215,f217,f219,f234,f277,f282,f327,f433,f438,f443,f448,f602,f652,f660,f662,f957,f960,f964,f966,f968,f972,f1027,f1028,f1031,f1069,f1093,f1094,f1095,f1096])).
% 0.21/0.53  fof(f1096,plain,(
% 0.21/0.53    spl8_4 | ~spl8_21 | ~spl8_22 | ~spl8_24),
% 0.21/0.53    inference(avatar_split_clause,[],[f1042,f231,f195,f189,f90])).
% 0.21/0.53  fof(f90,plain,(
% 0.21/0.53    spl8_4 <=> r1_tsep_1(sK7,sK6)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_4])])).
% 0.21/0.53  fof(f189,plain,(
% 0.21/0.53    spl8_21 <=> l1_struct_0(sK6)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_21])])).
% 0.21/0.53  fof(f195,plain,(
% 0.21/0.53    spl8_22 <=> l1_struct_0(sK7)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_22])])).
% 0.21/0.53  fof(f231,plain,(
% 0.21/0.53    spl8_24 <=> r1_tsep_1(sK6,sK7)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_24])])).
% 0.21/0.53  fof(f1042,plain,(
% 0.21/0.53    r1_tsep_1(sK7,sK6) | (~spl8_21 | ~spl8_22 | ~spl8_24)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f191,f197,f233,f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0,X1] : (r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f17])).
% 0.21/0.53  fof(f17,plain,(
% 0.21/0.53    ! [X0,X1] : ((r1_tsep_1(X1,X0) | ~r1_tsep_1(X0,X1)) | (~l1_struct_0(X1) | ~l1_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0,X1] : ((l1_struct_0(X1) & l1_struct_0(X0)) => (r1_tsep_1(X0,X1) => r1_tsep_1(X1,X0)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_tsep_1)).
% 0.21/0.53  fof(f233,plain,(
% 0.21/0.53    r1_tsep_1(sK6,sK7) | ~spl8_24),
% 0.21/0.53    inference(avatar_component_clause,[],[f231])).
% 0.21/0.53  fof(f197,plain,(
% 0.21/0.53    l1_struct_0(sK7) | ~spl8_22),
% 0.21/0.53    inference(avatar_component_clause,[],[f195])).
% 0.21/0.53  fof(f191,plain,(
% 0.21/0.53    l1_struct_0(sK6) | ~spl8_21),
% 0.21/0.53    inference(avatar_component_clause,[],[f189])).
% 0.21/0.53  fof(f1095,plain,(
% 0.21/0.53    spl8_28 | ~spl8_3 | ~spl8_20 | ~spl8_22),
% 0.21/0.53    inference(avatar_split_clause,[],[f983,f195,f183,f86,f279])).
% 0.21/0.53  fof(f279,plain,(
% 0.21/0.53    spl8_28 <=> r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_28])])).
% 0.21/0.53  fof(f86,plain,(
% 0.21/0.53    spl8_3 <=> r1_tsep_1(sK7,sK5)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_3])])).
% 0.21/0.53  fof(f183,plain,(
% 0.21/0.53    spl8_20 <=> l1_struct_0(sK5)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_20])])).
% 0.21/0.53  fof(f983,plain,(
% 0.21/0.53    r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5)) | (~spl8_3 | ~spl8_20 | ~spl8_22)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f197,f185,f87,f62])).
% 0.21/0.53  fof(f62,plain,(
% 0.21/0.53    ( ! [X0,X1] : (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f39,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (((r1_tsep_1(X0,X1) | ~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) & (r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | ~r1_tsep_1(X0,X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f12])).
% 0.21/0.53  fof(f12,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : ((r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => (r1_tsep_1(X0,X1) <=> r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tsep_1)).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    r1_tsep_1(sK7,sK5) | ~spl8_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f86])).
% 0.21/0.53  fof(f185,plain,(
% 0.21/0.53    l1_struct_0(sK5) | ~spl8_20),
% 0.21/0.53    inference(avatar_component_clause,[],[f183])).
% 0.21/0.53  fof(f1094,plain,(
% 0.21/0.53    spl8_27 | ~spl8_4 | ~spl8_21 | ~spl8_22),
% 0.21/0.53    inference(avatar_split_clause,[],[f1033,f195,f189,f90,f274])).
% 0.21/0.53  fof(f274,plain,(
% 0.21/0.53    spl8_27 <=> r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_27])])).
% 0.21/0.53  fof(f1033,plain,(
% 0.21/0.53    r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)) | (~spl8_4 | ~spl8_21 | ~spl8_22)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f197,f191,f91,f62])).
% 0.21/0.53  fof(f91,plain,(
% 0.21/0.53    r1_tsep_1(sK7,sK6) | ~spl8_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f90])).
% 0.21/0.53  fof(f1093,plain,(
% 0.21/0.53    ~spl8_27 | ~spl8_28 | spl8_129),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f1092])).
% 0.21/0.53  fof(f1092,plain,(
% 0.21/0.53    $false | (~spl8_27 | ~spl8_28 | spl8_129)),
% 0.21/0.53    inference(subsumption_resolution,[],[f1084,f979])).
% 0.21/0.53  fof(f979,plain,(
% 0.21/0.53    ~r1_xboole_0(u1_struct_0(sK7),k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6))) | spl8_129),
% 0.21/0.53    inference(avatar_component_clause,[],[f978])).
% 0.21/0.53  fof(f978,plain,(
% 0.21/0.53    spl8_129 <=> r1_xboole_0(u1_struct_0(sK7),k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_129])])).
% 0.21/0.53  fof(f1084,plain,(
% 0.21/0.53    r1_xboole_0(u1_struct_0(sK7),k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6))) | (~spl8_27 | ~spl8_28)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f275,f280,f69])).
% 0.21/0.53  fof(f69,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (r1_xboole_0(X0,k2_xboole_0(X1,X2)) | ~r1_xboole_0(X0,X1) | ~r1_xboole_0(X0,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | (r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & (~r1_xboole_0(X0,X2) | ~r1_xboole_0(X0,X1) | r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.53    inference(ennf_transformation,[],[f1])).
% 0.21/0.53  fof(f1,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : (~(r1_xboole_0(X0,k2_xboole_0(X1,X2)) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1))) & ~(r1_xboole_0(X0,X2) & r1_xboole_0(X0,X1) & ~r1_xboole_0(X0,k2_xboole_0(X1,X2))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).
% 0.21/0.53  fof(f280,plain,(
% 0.21/0.53    r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5)) | ~spl8_28),
% 0.21/0.53    inference(avatar_component_clause,[],[f279])).
% 0.21/0.53  fof(f275,plain,(
% 0.21/0.53    r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)) | ~spl8_27),
% 0.21/0.53    inference(avatar_component_clause,[],[f274])).
% 0.21/0.53  fof(f1069,plain,(
% 0.21/0.53    ~spl8_129 | spl8_6 | ~spl8_22 | ~spl8_77 | ~spl8_128),
% 0.21/0.53    inference(avatar_split_clause,[],[f1066,f954,f599,f195,f99,f978])).
% 0.21/0.53  fof(f99,plain,(
% 0.21/0.53    spl8_6 <=> r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_6])])).
% 0.21/0.53  fof(f599,plain,(
% 0.21/0.53    spl8_77 <=> l1_struct_0(k1_tsep_1(sK4,sK5,sK6))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_77])])).
% 0.21/0.53  fof(f954,plain,(
% 0.21/0.53    spl8_128 <=> u1_struct_0(k1_tsep_1(sK4,sK5,sK6)) = k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_128])])).
% 0.21/0.53  fof(f1066,plain,(
% 0.21/0.53    ~r1_xboole_0(u1_struct_0(sK7),k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6))) | (spl8_6 | ~spl8_22 | ~spl8_77 | ~spl8_128)),
% 0.21/0.53    inference(forward_demodulation,[],[f1059,f956])).
% 0.21/0.53  fof(f956,plain,(
% 0.21/0.53    u1_struct_0(k1_tsep_1(sK4,sK5,sK6)) = k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6)) | ~spl8_128),
% 0.21/0.53    inference(avatar_component_clause,[],[f954])).
% 0.21/0.53  fof(f1059,plain,(
% 0.21/0.53    ~r1_xboole_0(u1_struct_0(sK7),u1_struct_0(k1_tsep_1(sK4,sK5,sK6))) | (spl8_6 | ~spl8_22 | ~spl8_77)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f197,f601,f100,f63])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~r1_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) | r1_tsep_1(X0,X1) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f39])).
% 0.21/0.53  fof(f100,plain,(
% 0.21/0.53    ~r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6)) | spl8_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f99])).
% 0.21/0.53  fof(f601,plain,(
% 0.21/0.53    l1_struct_0(k1_tsep_1(sK4,sK5,sK6)) | ~spl8_77),
% 0.21/0.53    inference(avatar_component_clause,[],[f599])).
% 0.21/0.53  fof(f1031,plain,(
% 0.21/0.53    ~spl8_24 | ~spl8_1 | ~spl8_23),
% 0.21/0.53    inference(avatar_split_clause,[],[f1030,f211,f78,f231])).
% 0.21/0.53  fof(f78,plain,(
% 0.21/0.53    spl8_1 <=> sP2(sK7,sK6,sK5,sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_1])])).
% 0.21/0.53  fof(f211,plain,(
% 0.21/0.53    spl8_23 <=> r1_tsep_1(sK5,sK7)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_23])])).
% 0.21/0.53  fof(f1030,plain,(
% 0.21/0.53    ~r1_tsep_1(sK6,sK7) | (~spl8_1 | ~spl8_23)),
% 0.21/0.53    inference(subsumption_resolution,[],[f997,f213])).
% 0.21/0.53  fof(f213,plain,(
% 0.21/0.53    r1_tsep_1(sK5,sK7) | ~spl8_23),
% 0.21/0.53    inference(avatar_component_clause,[],[f211])).
% 0.21/0.53  fof(f997,plain,(
% 0.21/0.53    ~r1_tsep_1(sK5,sK7) | ~r1_tsep_1(sK6,sK7) | ~spl8_1),
% 0.21/0.53    inference(resolution,[],[f80,f44])).
% 0.21/0.53  fof(f44,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~sP2(X0,X1,X2,X3) | ~r1_tsep_1(X2,X0) | ~r1_tsep_1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f29,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : (((~r1_tsep_1(X1,X0) | ~r1_tsep_1(X2,X0)) & r1_tsep_1(k1_tsep_1(X3,X2,X1),X0)) | ~sP2(X0,X1,X2,X3))),
% 0.21/0.53    inference(rectify,[],[f28])).
% 0.21/0.53  fof(f28,plain,(
% 0.21/0.53    ! [X3,X2,X1,X0] : (((~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3)) & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)) | ~sP2(X3,X2,X1,X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f24])).
% 0.21/0.53  fof(f24,plain,(
% 0.21/0.53    ! [X3,X2,X1,X0] : (((~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3)) & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)) | ~sP2(X3,X2,X1,X0))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP2])])).
% 0.21/0.53  fof(f80,plain,(
% 0.21/0.53    sP2(sK7,sK6,sK5,sK4) | ~spl8_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f78])).
% 0.21/0.53  fof(f1028,plain,(
% 0.21/0.53    spl8_83 | ~spl8_1),
% 0.21/0.53    inference(avatar_split_clause,[],[f995,f78,f644])).
% 0.21/0.53  fof(f644,plain,(
% 0.21/0.53    spl8_83 <=> r1_tsep_1(k1_tsep_1(sK4,sK5,sK6),sK7)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_83])])).
% 0.21/0.53  fof(f995,plain,(
% 0.21/0.53    r1_tsep_1(k1_tsep_1(sK4,sK5,sK6),sK7) | ~spl8_1),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f80,f43])).
% 0.21/0.53  fof(f43,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (r1_tsep_1(k1_tsep_1(X3,X2,X1),X0) | ~sP2(X0,X1,X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f29])).
% 0.21/0.53  fof(f1027,plain,(
% 0.21/0.53    ~spl8_83 | spl8_6 | ~spl8_22 | ~spl8_77),
% 0.21/0.53    inference(avatar_split_clause,[],[f1011,f599,f195,f99,f644])).
% 0.21/0.53  fof(f1011,plain,(
% 0.21/0.53    ~r1_tsep_1(k1_tsep_1(sK4,sK5,sK6),sK7) | (spl8_6 | ~spl8_22 | ~spl8_77)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f197,f601,f100,f68])).
% 0.21/0.53  fof(f972,plain,(
% 0.21/0.53    ~spl8_2 | ~spl8_6 | ~spl8_22 | ~spl8_77),
% 0.21/0.53    inference(avatar_split_clause,[],[f670,f599,f195,f99,f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    spl8_2 <=> sP0(sK7,sK6,sK5,sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_2])])).
% 0.21/0.53  fof(f670,plain,(
% 0.21/0.53    ~sP0(sK7,sK6,sK5,sK4) | (~spl8_6 | ~spl8_22 | ~spl8_77)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f197,f601,f101,f254])).
% 0.21/0.53  fof(f254,plain,(
% 0.21/0.53    ( ! [X6,X4,X7,X5] : (~r1_tsep_1(X4,k1_tsep_1(X7,X6,X5)) | ~sP0(X4,X5,X6,X7) | ~l1_struct_0(k1_tsep_1(X7,X6,X5)) | ~l1_struct_0(X4)) )),
% 0.21/0.53    inference(resolution,[],[f50,f68])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(k1_tsep_1(X3,X2,X1),X0) | ~sP0(X0,X1,X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((~r1_tsep_1(k1_tsep_1(X3,X2,X1),X0) & r1_tsep_1(X1,X0) & r1_tsep_1(X2,X0)) | ~sP0(X0,X1,X2,X3))),
% 0.21/0.53    inference(rectify,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X3,X2,X1,X0] : ((~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3)) | ~sP0(X3,X2,X1,X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f22])).
% 0.21/0.53  fof(f22,plain,(
% 0.21/0.53    ! [X3,X2,X1,X0] : ((~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3)) | ~sP0(X3,X2,X1,X0))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.53  fof(f101,plain,(
% 0.21/0.53    r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6)) | ~spl8_6),
% 0.21/0.53    inference(avatar_component_clause,[],[f99])).
% 0.21/0.53  fof(f968,plain,(
% 0.21/0.53    ~spl8_5 | ~spl8_6),
% 0.21/0.53    inference(avatar_split_clause,[],[f671,f99,f94])).
% 0.21/0.53  fof(f94,plain,(
% 0.21/0.53    spl8_5 <=> sP1(sK6,sK5,sK4,sK7)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_5])])).
% 0.21/0.53  fof(f671,plain,(
% 0.21/0.53    ~sP1(sK6,sK5,sK4,sK7) | ~spl8_6),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f101,f47])).
% 0.21/0.53  fof(f47,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~r1_tsep_1(X3,k1_tsep_1(X2,X1,X0)) | ~sP1(X0,X1,X2,X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1,X2,X3] : ((~r1_tsep_1(X3,k1_tsep_1(X2,X1,X0)) & r1_tsep_1(X3,X0) & r1_tsep_1(X3,X1)) | ~sP1(X0,X1,X2,X3))),
% 0.21/0.53    inference(rectify,[],[f30])).
% 0.21/0.53  fof(f30,plain,(
% 0.21/0.53    ! [X2,X1,X0,X3] : ((~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1)) | ~sP1(X2,X1,X0,X3))),
% 0.21/0.53    inference(nnf_transformation,[],[f23])).
% 0.21/0.53  fof(f23,plain,(
% 0.21/0.53    ! [X2,X1,X0,X3] : ((~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1)) | ~sP1(X2,X1,X0,X3))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 0.21/0.53  fof(f966,plain,(
% 0.21/0.53    spl8_27 | ~spl8_84 | ~spl8_128),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f965])).
% 0.21/0.53  fof(f965,plain,(
% 0.21/0.53    $false | (spl8_27 | ~spl8_84 | ~spl8_128)),
% 0.21/0.53    inference(subsumption_resolution,[],[f958,f288])).
% 0.21/0.53  fof(f288,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_xboole_0(u1_struct_0(sK7),k2_xboole_0(X0,u1_struct_0(sK6)))) ) | spl8_27),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f276,f71])).
% 0.21/0.53  fof(f71,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f276,plain,(
% 0.21/0.53    ~r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)) | spl8_27),
% 0.21/0.53    inference(avatar_component_clause,[],[f274])).
% 0.21/0.53  fof(f958,plain,(
% 0.21/0.53    r1_xboole_0(u1_struct_0(sK7),k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6))) | (~spl8_84 | ~spl8_128)),
% 0.21/0.53    inference(backward_demodulation,[],[f651,f956])).
% 0.21/0.53  fof(f651,plain,(
% 0.21/0.53    r1_xboole_0(u1_struct_0(sK7),u1_struct_0(k1_tsep_1(sK4,sK5,sK6))) | ~spl8_84),
% 0.21/0.53    inference(avatar_component_clause,[],[f649])).
% 0.21/0.53  fof(f649,plain,(
% 0.21/0.53    spl8_84 <=> r1_xboole_0(u1_struct_0(sK7),u1_struct_0(k1_tsep_1(sK4,sK5,sK6)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_84])])).
% 0.21/0.53  fof(f964,plain,(
% 0.21/0.53    ~spl8_3 | ~spl8_20 | ~spl8_22 | spl8_23),
% 0.21/0.53    inference(avatar_split_clause,[],[f664,f211,f195,f183,f86])).
% 0.21/0.53  fof(f664,plain,(
% 0.21/0.53    ~r1_tsep_1(sK7,sK5) | (~spl8_20 | ~spl8_22 | spl8_23)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f197,f185,f212,f68])).
% 0.21/0.53  fof(f212,plain,(
% 0.21/0.53    ~r1_tsep_1(sK5,sK7) | spl8_23),
% 0.21/0.53    inference(avatar_component_clause,[],[f211])).
% 0.21/0.53  fof(f960,plain,(
% 0.21/0.53    spl8_28 | ~spl8_84 | ~spl8_128),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f959])).
% 0.21/0.53  fof(f959,plain,(
% 0.21/0.53    $false | (spl8_28 | ~spl8_84 | ~spl8_128)),
% 0.21/0.53    inference(subsumption_resolution,[],[f958,f293])).
% 0.21/0.53  fof(f293,plain,(
% 0.21/0.53    ( ! [X0] : (~r1_xboole_0(u1_struct_0(sK7),k2_xboole_0(u1_struct_0(sK5),X0))) ) | spl8_28),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f281,f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~r1_xboole_0(X0,k2_xboole_0(X1,X2)) | r1_xboole_0(X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f281,plain,(
% 0.21/0.53    ~r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5)) | spl8_28),
% 0.21/0.53    inference(avatar_component_clause,[],[f279])).
% 0.21/0.53  fof(f957,plain,(
% 0.21/0.53    spl8_128 | ~spl8_9 | spl8_10 | ~spl8_11 | spl8_12 | ~spl8_13 | spl8_15 | spl8_50 | ~spl8_51 | ~spl8_52),
% 0.21/0.53    inference(avatar_split_clause,[],[f870,f440,f435,f430,f144,f134,f129,f124,f119,f114,f954])).
% 0.21/0.53  fof(f114,plain,(
% 0.21/0.53    spl8_9 <=> m1_pre_topc(sK6,sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_9])])).
% 0.21/0.53  fof(f119,plain,(
% 0.21/0.53    spl8_10 <=> v2_struct_0(sK6)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_10])])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    spl8_11 <=> m1_pre_topc(sK5,sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_11])])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    spl8_12 <=> v2_struct_0(sK5)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_12])])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    spl8_13 <=> l1_pre_topc(sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_13])])).
% 0.21/0.53  fof(f144,plain,(
% 0.21/0.53    spl8_15 <=> v2_struct_0(sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_15])])).
% 0.21/0.53  fof(f430,plain,(
% 0.21/0.53    spl8_50 <=> v2_struct_0(k1_tsep_1(sK4,sK5,sK6))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_50])])).
% 0.21/0.53  fof(f435,plain,(
% 0.21/0.53    spl8_51 <=> v1_pre_topc(k1_tsep_1(sK4,sK5,sK6))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_51])])).
% 0.21/0.53  fof(f440,plain,(
% 0.21/0.53    spl8_52 <=> m1_pre_topc(k1_tsep_1(sK4,sK5,sK6),sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_52])])).
% 0.21/0.53  fof(f870,plain,(
% 0.21/0.53    u1_struct_0(k1_tsep_1(sK4,sK5,sK6)) = k2_xboole_0(u1_struct_0(sK5),u1_struct_0(sK6)) | (~spl8_9 | spl8_10 | ~spl8_11 | spl8_12 | ~spl8_13 | spl8_15 | spl8_50 | ~spl8_51 | ~spl8_52)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f146,f136,f131,f121,f126,f116,f432,f437,f442,f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(equality_resolution,[],[f66])).
% 0.21/0.53  fof(f66,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f40])).
% 0.21/0.53  fof(f40,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(nnf_transformation,[],[f16])).
% 0.21/0.53  fof(f16,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f15])).
% 0.21/0.53  fof(f15,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f4])).
% 0.21/0.53  fof(f4,axiom,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).
% 0.21/0.53  fof(f442,plain,(
% 0.21/0.53    m1_pre_topc(k1_tsep_1(sK4,sK5,sK6),sK4) | ~spl8_52),
% 0.21/0.53    inference(avatar_component_clause,[],[f440])).
% 0.21/0.53  fof(f437,plain,(
% 0.21/0.53    v1_pre_topc(k1_tsep_1(sK4,sK5,sK6)) | ~spl8_51),
% 0.21/0.53    inference(avatar_component_clause,[],[f435])).
% 0.21/0.53  fof(f432,plain,(
% 0.21/0.53    ~v2_struct_0(k1_tsep_1(sK4,sK5,sK6)) | spl8_50),
% 0.21/0.53    inference(avatar_component_clause,[],[f430])).
% 0.21/0.53  fof(f116,plain,(
% 0.21/0.53    m1_pre_topc(sK6,sK4) | ~spl8_9),
% 0.21/0.53    inference(avatar_component_clause,[],[f114])).
% 0.21/0.53  fof(f126,plain,(
% 0.21/0.53    m1_pre_topc(sK5,sK4) | ~spl8_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f124])).
% 0.21/0.53  fof(f121,plain,(
% 0.21/0.53    ~v2_struct_0(sK6) | spl8_10),
% 0.21/0.53    inference(avatar_component_clause,[],[f119])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    ~v2_struct_0(sK5) | spl8_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f129])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    l1_pre_topc(sK4) | ~spl8_13),
% 0.21/0.53    inference(avatar_component_clause,[],[f134])).
% 0.21/0.53  fof(f146,plain,(
% 0.21/0.53    ~v2_struct_0(sK4) | spl8_15),
% 0.21/0.53    inference(avatar_component_clause,[],[f144])).
% 0.21/0.53  fof(f662,plain,(
% 0.21/0.53    ~spl8_2 | spl8_24),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f661])).
% 0.21/0.53  fof(f661,plain,(
% 0.21/0.53    $false | (~spl8_2 | spl8_24)),
% 0.21/0.53    inference(subsumption_resolution,[],[f84,f243])).
% 0.21/0.53  fof(f243,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~sP0(sK7,sK6,X0,X1)) ) | spl8_24),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f232,f49])).
% 0.21/0.53  fof(f49,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | r1_tsep_1(X1,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f232,plain,(
% 0.21/0.53    ~r1_tsep_1(sK6,sK7) | spl8_24),
% 0.21/0.53    inference(avatar_component_clause,[],[f231])).
% 0.21/0.53  fof(f84,plain,(
% 0.21/0.53    sP0(sK7,sK6,sK5,sK4) | ~spl8_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f82])).
% 0.21/0.53  fof(f660,plain,(
% 0.21/0.53    ~spl8_23 | spl8_3 | ~spl8_20 | ~spl8_22),
% 0.21/0.53    inference(avatar_split_clause,[],[f226,f195,f183,f86,f211])).
% 0.21/0.53  fof(f226,plain,(
% 0.21/0.53    ~r1_tsep_1(sK5,sK7) | (spl8_3 | ~spl8_20 | ~spl8_22)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f185,f197,f88,f68])).
% 0.21/0.53  fof(f88,plain,(
% 0.21/0.53    ~r1_tsep_1(sK7,sK5) | spl8_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f86])).
% 0.21/0.53  fof(f652,plain,(
% 0.21/0.53    spl8_84 | ~spl8_6 | ~spl8_22 | ~spl8_77),
% 0.21/0.53    inference(avatar_split_clause,[],[f641,f599,f195,f99,f649])).
% 0.21/0.53  fof(f641,plain,(
% 0.21/0.53    r1_xboole_0(u1_struct_0(sK7),u1_struct_0(k1_tsep_1(sK4,sK5,sK6))) | (~spl8_6 | ~spl8_22 | ~spl8_77)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f197,f101,f601,f62])).
% 0.21/0.53  fof(f602,plain,(
% 0.21/0.53    spl8_77 | ~spl8_53),
% 0.21/0.53    inference(avatar_split_clause,[],[f597,f445,f599])).
% 0.21/0.53  fof(f445,plain,(
% 0.21/0.53    spl8_53 <=> l1_pre_topc(k1_tsep_1(sK4,sK5,sK6))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_53])])).
% 0.21/0.53  fof(f597,plain,(
% 0.21/0.53    l1_struct_0(k1_tsep_1(sK4,sK5,sK6)) | ~spl8_53),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f447,f64])).
% 0.21/0.53  fof(f64,plain,(
% 0.21/0.53    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f13])).
% 0.21/0.53  fof(f13,plain,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.53  fof(f447,plain,(
% 0.21/0.53    l1_pre_topc(k1_tsep_1(sK4,sK5,sK6)) | ~spl8_53),
% 0.21/0.53    inference(avatar_component_clause,[],[f445])).
% 0.21/0.53  fof(f448,plain,(
% 0.21/0.53    spl8_53 | ~spl8_13 | ~spl8_32),
% 0.21/0.53    inference(avatar_split_clause,[],[f425,f324,f134,f445])).
% 0.21/0.53  fof(f324,plain,(
% 0.21/0.53    spl8_32 <=> sP3(sK4,sK6,sK5)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_32])])).
% 0.21/0.53  fof(f425,plain,(
% 0.21/0.53    l1_pre_topc(k1_tsep_1(sK4,sK5,sK6)) | (~spl8_13 | ~spl8_32)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f136,f326,f241])).
% 0.21/0.53  fof(f241,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (l1_pre_topc(k1_tsep_1(X0,X2,X1)) | ~sP3(X0,X1,X2) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(resolution,[],[f74,f65])).
% 0.21/0.53  fof(f65,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f14])).
% 0.21/0.53  fof(f14,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f3])).
% 0.21/0.53  fof(f3,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X2,X1),X0) | ~sP3(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f42])).
% 0.21/0.53  fof(f42,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X2,X1),X0) & v1_pre_topc(k1_tsep_1(X0,X2,X1)) & ~v2_struct_0(k1_tsep_1(X0,X2,X1))) | ~sP3(X0,X1,X2))),
% 0.21/0.53    inference(rectify,[],[f41])).
% 0.21/0.53  fof(f41,plain,(
% 0.21/0.53    ! [X0,X2,X1] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP3(X0,X2,X1))),
% 0.21/0.53    inference(nnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0,X2,X1] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP3(X0,X2,X1))),
% 0.21/0.53    introduced(predicate_definition_introduction,[new_symbols(naming,[sP3])])).
% 0.21/0.53  fof(f326,plain,(
% 0.21/0.53    sP3(sK4,sK6,sK5) | ~spl8_32),
% 0.21/0.53    inference(avatar_component_clause,[],[f324])).
% 0.21/0.53  fof(f443,plain,(
% 0.21/0.53    spl8_52 | ~spl8_32),
% 0.21/0.53    inference(avatar_split_clause,[],[f426,f324,f440])).
% 0.21/0.53  fof(f426,plain,(
% 0.21/0.53    m1_pre_topc(k1_tsep_1(sK4,sK5,sK6),sK4) | ~spl8_32),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f326,f74])).
% 0.21/0.53  fof(f438,plain,(
% 0.21/0.53    spl8_51 | ~spl8_32),
% 0.21/0.53    inference(avatar_split_clause,[],[f427,f324,f435])).
% 0.21/0.53  fof(f427,plain,(
% 0.21/0.53    v1_pre_topc(k1_tsep_1(sK4,sK5,sK6)) | ~spl8_32),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f326,f73])).
% 0.21/0.53  fof(f73,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X2,X1)) | ~sP3(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f42])).
% 0.21/0.53  fof(f433,plain,(
% 0.21/0.53    ~spl8_50 | ~spl8_32),
% 0.21/0.53    inference(avatar_split_clause,[],[f428,f324,f430])).
% 0.21/0.53  fof(f428,plain,(
% 0.21/0.53    ~v2_struct_0(k1_tsep_1(sK4,sK5,sK6)) | ~spl8_32),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f326,f72])).
% 0.21/0.53  fof(f72,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X2,X1)) | ~sP3(X0,X1,X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f42])).
% 0.21/0.53  fof(f327,plain,(
% 0.21/0.53    spl8_32 | ~spl8_9 | spl8_10 | ~spl8_11 | spl8_12 | ~spl8_13 | spl8_15),
% 0.21/0.53    inference(avatar_split_clause,[],[f304,f144,f134,f129,f124,f119,f114,f324])).
% 0.21/0.53  fof(f304,plain,(
% 0.21/0.53    sP3(sK4,sK6,sK5) | (~spl8_9 | spl8_10 | ~spl8_11 | spl8_12 | ~spl8_13 | spl8_15)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f146,f136,f131,f126,f121,f116,f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (sP3(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f27])).
% 0.21/0.53  fof(f27,plain,(
% 0.21/0.53    ! [X0,X1,X2] : (sP3(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(definition_folding,[],[f21,f26])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f6])).
% 0.21/0.53  fof(f6,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 0.21/0.53  fof(f282,plain,(
% 0.21/0.53    ~spl8_28 | spl8_3 | ~spl8_20 | ~spl8_22),
% 0.21/0.53    inference(avatar_split_clause,[],[f257,f195,f183,f86,f279])).
% 0.21/0.53  fof(f257,plain,(
% 0.21/0.53    ~r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK5)) | (spl8_3 | ~spl8_20 | ~spl8_22)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f197,f185,f88,f63])).
% 0.21/0.53  fof(f277,plain,(
% 0.21/0.53    ~spl8_27 | spl8_4 | ~spl8_21 | ~spl8_22),
% 0.21/0.53    inference(avatar_split_clause,[],[f258,f195,f189,f90,f274])).
% 0.21/0.53  fof(f258,plain,(
% 0.21/0.53    ~r1_xboole_0(u1_struct_0(sK7),u1_struct_0(sK6)) | (spl8_4 | ~spl8_21 | ~spl8_22)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f197,f191,f92,f63])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    ~r1_tsep_1(sK7,sK6) | spl8_4),
% 0.21/0.53    inference(avatar_component_clause,[],[f90])).
% 0.21/0.53  fof(f234,plain,(
% 0.21/0.53    spl8_24 | ~spl8_4 | ~spl8_21 | ~spl8_22),
% 0.21/0.53    inference(avatar_split_clause,[],[f225,f195,f189,f90,f231])).
% 0.21/0.53  fof(f225,plain,(
% 0.21/0.53    r1_tsep_1(sK6,sK7) | (~spl8_4 | ~spl8_21 | ~spl8_22)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f197,f191,f91,f68])).
% 0.21/0.53  fof(f219,plain,(
% 0.21/0.53    spl8_3 | ~spl8_5),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f218])).
% 0.21/0.53  fof(f218,plain,(
% 0.21/0.53    $false | (spl8_3 | ~spl8_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f96,f199])).
% 0.21/0.53  fof(f199,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~sP1(X0,sK5,X1,sK7)) ) | spl8_3),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f88,f45])).
% 0.21/0.53  fof(f45,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3) | r1_tsep_1(X3,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f96,plain,(
% 0.21/0.53    sP1(sK6,sK5,sK4,sK7) | ~spl8_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f94])).
% 0.21/0.53  fof(f217,plain,(
% 0.21/0.53    spl8_4 | ~spl8_5),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f216])).
% 0.21/0.53  fof(f216,plain,(
% 0.21/0.53    $false | (spl8_4 | ~spl8_5)),
% 0.21/0.53    inference(subsumption_resolution,[],[f96,f203])).
% 0.21/0.53  fof(f203,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~sP1(sK6,X0,X1,sK7)) ) | spl8_4),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f92,f46])).
% 0.21/0.53  fof(f46,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~sP1(X0,X1,X2,X3) | r1_tsep_1(X3,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f31])).
% 0.21/0.53  fof(f215,plain,(
% 0.21/0.53    spl8_23 | ~spl8_2),
% 0.21/0.53    inference(avatar_split_clause,[],[f209,f82,f211])).
% 0.21/0.53  fof(f209,plain,(
% 0.21/0.53    r1_tsep_1(sK5,sK7) | ~spl8_2),
% 0.21/0.53    inference(resolution,[],[f48,f84])).
% 0.21/0.53  fof(f48,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (~sP0(X0,X1,X2,X3) | r1_tsep_1(X2,X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f33])).
% 0.21/0.53  fof(f198,plain,(
% 0.21/0.53    spl8_22 | ~spl8_19),
% 0.21/0.53    inference(avatar_split_clause,[],[f193,f171,f195])).
% 0.21/0.53  fof(f171,plain,(
% 0.21/0.53    spl8_19 <=> l1_pre_topc(sK7)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_19])])).
% 0.21/0.53  fof(f193,plain,(
% 0.21/0.53    l1_struct_0(sK7) | ~spl8_19),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f173,f64])).
% 0.21/0.53  fof(f173,plain,(
% 0.21/0.53    l1_pre_topc(sK7) | ~spl8_19),
% 0.21/0.53    inference(avatar_component_clause,[],[f171])).
% 0.21/0.53  fof(f192,plain,(
% 0.21/0.53    spl8_21 | ~spl8_18),
% 0.21/0.53    inference(avatar_split_clause,[],[f187,f166,f189])).
% 0.21/0.53  fof(f166,plain,(
% 0.21/0.53    spl8_18 <=> l1_pre_topc(sK6)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_18])])).
% 0.21/0.53  fof(f187,plain,(
% 0.21/0.53    l1_struct_0(sK6) | ~spl8_18),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f168,f64])).
% 0.21/0.53  fof(f168,plain,(
% 0.21/0.53    l1_pre_topc(sK6) | ~spl8_18),
% 0.21/0.53    inference(avatar_component_clause,[],[f166])).
% 0.21/0.53  fof(f186,plain,(
% 0.21/0.53    spl8_20 | ~spl8_17),
% 0.21/0.53    inference(avatar_split_clause,[],[f181,f161,f183])).
% 0.21/0.53  fof(f161,plain,(
% 0.21/0.53    spl8_17 <=> l1_pre_topc(sK5)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_17])])).
% 0.21/0.53  fof(f181,plain,(
% 0.21/0.53    l1_struct_0(sK5) | ~spl8_17),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f163,f64])).
% 0.21/0.53  fof(f163,plain,(
% 0.21/0.53    l1_pre_topc(sK5) | ~spl8_17),
% 0.21/0.53    inference(avatar_component_clause,[],[f161])).
% 0.21/0.53  fof(f180,plain,(
% 0.21/0.53    spl8_17 | ~spl8_11 | ~spl8_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f179,f134,f124,f161])).
% 0.21/0.53  fof(f179,plain,(
% 0.21/0.53    l1_pre_topc(sK5) | (~spl8_11 | ~spl8_13)),
% 0.21/0.53    inference(subsumption_resolution,[],[f159,f136])).
% 0.21/0.53  fof(f159,plain,(
% 0.21/0.53    l1_pre_topc(sK5) | ~l1_pre_topc(sK4) | ~spl8_11),
% 0.21/0.53    inference(resolution,[],[f65,f126])).
% 0.21/0.53  fof(f178,plain,(
% 0.21/0.53    spl8_18 | ~spl8_9 | ~spl8_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f177,f134,f114,f166])).
% 0.21/0.53  fof(f177,plain,(
% 0.21/0.53    l1_pre_topc(sK6) | (~spl8_9 | ~spl8_13)),
% 0.21/0.53    inference(subsumption_resolution,[],[f158,f136])).
% 0.21/0.53  fof(f158,plain,(
% 0.21/0.53    l1_pre_topc(sK6) | ~l1_pre_topc(sK4) | ~spl8_9),
% 0.21/0.53    inference(resolution,[],[f65,f116])).
% 0.21/0.53  fof(f176,plain,(
% 0.21/0.53    spl8_19 | ~spl8_7 | ~spl8_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f175,f134,f104,f171])).
% 0.21/0.53  fof(f104,plain,(
% 0.21/0.53    spl8_7 <=> m1_pre_topc(sK7,sK4)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl8_7])])).
% 0.21/0.53  fof(f175,plain,(
% 0.21/0.53    l1_pre_topc(sK7) | (~spl8_7 | ~spl8_13)),
% 0.21/0.53    inference(subsumption_resolution,[],[f157,f136])).
% 0.21/0.53  fof(f157,plain,(
% 0.21/0.53    l1_pre_topc(sK7) | ~l1_pre_topc(sK4) | ~spl8_7),
% 0.21/0.53    inference(resolution,[],[f65,f106])).
% 0.21/0.53  fof(f106,plain,(
% 0.21/0.53    m1_pre_topc(sK7,sK4) | ~spl8_7),
% 0.21/0.53    inference(avatar_component_clause,[],[f104])).
% 0.21/0.53  fof(f147,plain,(
% 0.21/0.53    ~spl8_15),
% 0.21/0.53    inference(avatar_split_clause,[],[f51,f144])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ~v2_struct_0(sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  fof(f38,plain,(
% 0.21/0.53    ((((sP1(sK6,sK5,sK4,sK7) | ((~r1_tsep_1(sK7,sK6) | ~r1_tsep_1(sK7,sK5)) & r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6))) | sP0(sK7,sK6,sK5,sK4) | sP2(sK7,sK6,sK5,sK4)) & m1_pre_topc(sK7,sK4) & ~v2_struct_0(sK7)) & m1_pre_topc(sK6,sK4) & ~v2_struct_0(sK6)) & m1_pre_topc(sK5,sK4) & ~v2_struct_0(sK5)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4)),
% 0.21/0.53    inference(skolemisation,[status(esa),new_symbols(skolem,[sK4,sK5,sK6,sK7])],[f25,f37,f36,f35,f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((sP1(X2,X1,X0,X3) | ((~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1)) & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) | sP0(X3,X2,X1,X0) | sP2(X3,X2,X1,X0)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : ((sP1(X2,X1,sK4,X3) | ((~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1)) & r1_tsep_1(X3,k1_tsep_1(sK4,X1,X2))) | sP0(X3,X2,X1,sK4) | sP2(X3,X2,X1,sK4)) & m1_pre_topc(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK4) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK4) & ~v2_struct_0(X1)) & l1_pre_topc(sK4) & v2_pre_topc(sK4) & ~v2_struct_0(sK4))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f35,plain,(
% 0.21/0.53    ? [X1] : (? [X2] : (? [X3] : ((sP1(X2,X1,sK4,X3) | ((~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1)) & r1_tsep_1(X3,k1_tsep_1(sK4,X1,X2))) | sP0(X3,X2,X1,sK4) | sP2(X3,X2,X1,sK4)) & m1_pre_topc(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK4) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK4) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : ((sP1(X2,sK5,sK4,X3) | ((~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,sK5)) & r1_tsep_1(X3,k1_tsep_1(sK4,sK5,X2))) | sP0(X3,X2,sK5,sK4) | sP2(X3,X2,sK5,sK4)) & m1_pre_topc(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK4) & ~v2_struct_0(X2)) & m1_pre_topc(sK5,sK4) & ~v2_struct_0(sK5))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f36,plain,(
% 0.21/0.53    ? [X2] : (? [X3] : ((sP1(X2,sK5,sK4,X3) | ((~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,sK5)) & r1_tsep_1(X3,k1_tsep_1(sK4,sK5,X2))) | sP0(X3,X2,sK5,sK4) | sP2(X3,X2,sK5,sK4)) & m1_pre_topc(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK4) & ~v2_struct_0(X2)) => (? [X3] : ((sP1(sK6,sK5,sK4,X3) | ((~r1_tsep_1(X3,sK6) | ~r1_tsep_1(X3,sK5)) & r1_tsep_1(X3,k1_tsep_1(sK4,sK5,sK6))) | sP0(X3,sK6,sK5,sK4) | sP2(X3,sK6,sK5,sK4)) & m1_pre_topc(X3,sK4) & ~v2_struct_0(X3)) & m1_pre_topc(sK6,sK4) & ~v2_struct_0(sK6))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f37,plain,(
% 0.21/0.53    ? [X3] : ((sP1(sK6,sK5,sK4,X3) | ((~r1_tsep_1(X3,sK6) | ~r1_tsep_1(X3,sK5)) & r1_tsep_1(X3,k1_tsep_1(sK4,sK5,sK6))) | sP0(X3,sK6,sK5,sK4) | sP2(X3,sK6,sK5,sK4)) & m1_pre_topc(X3,sK4) & ~v2_struct_0(X3)) => ((sP1(sK6,sK5,sK4,sK7) | ((~r1_tsep_1(sK7,sK6) | ~r1_tsep_1(sK7,sK5)) & r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6))) | sP0(sK7,sK6,sK5,sK4) | sP2(sK7,sK6,sK5,sK4)) & m1_pre_topc(sK7,sK4) & ~v2_struct_0(sK7))),
% 0.21/0.53    introduced(choice_axiom,[])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((sP1(X2,X1,X0,X3) | ((~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1)) & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) | sP0(X3,X2,X1,X0) | sP2(X3,X2,X1,X0)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(definition_folding,[],[f11,f24,f23,f22])).
% 0.21/0.53  fof(f11,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1)) | ((~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1)) & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) | (~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3)) | ((~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3)) & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3))) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f10])).
% 0.21/0.53  fof(f10,plain,(
% 0.21/0.53    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) & (r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1))) | ((~r1_tsep_1(X3,X2) | ~r1_tsep_1(X3,X1)) & r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) | (~r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) & (r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3))) | ((~r1_tsep_1(X2,X3) | ~r1_tsep_1(X1,X3)) & r1_tsep_1(k1_tsep_1(X0,X1,X2),X3))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,negated_conjecture,(
% 0.21/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (((r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1)) => r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) & (r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) => (r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1))) & ((r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3)) => r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)) & (r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) => (r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3))))))))),
% 0.21/0.53    inference(negated_conjecture,[],[f8])).
% 0.21/0.53  fof(f8,conjecture,(
% 0.21/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (((r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1)) => r1_tsep_1(X3,k1_tsep_1(X0,X1,X2))) & (r1_tsep_1(X3,k1_tsep_1(X0,X1,X2)) => (r1_tsep_1(X3,X2) & r1_tsep_1(X3,X1))) & ((r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3)) => r1_tsep_1(k1_tsep_1(X0,X1,X2),X3)) & (r1_tsep_1(k1_tsep_1(X0,X1,X2),X3) => (r1_tsep_1(X2,X3) & r1_tsep_1(X1,X3))))))))),
% 0.21/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_tmap_1)).
% 0.21/0.53  fof(f137,plain,(
% 0.21/0.53    spl8_13),
% 0.21/0.53    inference(avatar_split_clause,[],[f53,f134])).
% 0.21/0.53  fof(f53,plain,(
% 0.21/0.53    l1_pre_topc(sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  fof(f132,plain,(
% 0.21/0.53    ~spl8_12),
% 0.21/0.53    inference(avatar_split_clause,[],[f54,f129])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ~v2_struct_0(sK5)),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  fof(f127,plain,(
% 0.21/0.53    spl8_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f55,f124])).
% 0.21/0.53  fof(f55,plain,(
% 0.21/0.53    m1_pre_topc(sK5,sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  fof(f122,plain,(
% 0.21/0.53    ~spl8_10),
% 0.21/0.53    inference(avatar_split_clause,[],[f56,f119])).
% 0.21/0.53  fof(f56,plain,(
% 0.21/0.53    ~v2_struct_0(sK6)),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    spl8_9),
% 0.21/0.53    inference(avatar_split_clause,[],[f57,f114])).
% 0.21/0.53  fof(f57,plain,(
% 0.21/0.53    m1_pre_topc(sK6,sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  fof(f107,plain,(
% 0.21/0.53    spl8_7),
% 0.21/0.53    inference(avatar_split_clause,[],[f59,f104])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    m1_pre_topc(sK7,sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    spl8_1 | spl8_2 | spl8_6 | spl8_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f60,f94,f99,f82,f78])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    sP1(sK6,sK5,sK4,sK7) | r1_tsep_1(sK7,k1_tsep_1(sK4,sK5,sK6)) | sP0(sK7,sK6,sK5,sK4) | sP2(sK7,sK6,sK5,sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  fof(f97,plain,(
% 0.21/0.53    spl8_1 | spl8_2 | ~spl8_3 | ~spl8_4 | spl8_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f61,f94,f90,f86,f82,f78])).
% 0.21/0.53  fof(f61,plain,(
% 0.21/0.53    sP1(sK6,sK5,sK4,sK7) | ~r1_tsep_1(sK7,sK6) | ~r1_tsep_1(sK7,sK5) | sP0(sK7,sK6,sK5,sK4) | sP2(sK7,sK6,sK5,sK4)),
% 0.21/0.53    inference(cnf_transformation,[],[f38])).
% 0.21/0.53  % SZS output end Proof for theBenchmark
% 0.21/0.53  % (13941)------------------------------
% 0.21/0.53  % (13941)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13941)Termination reason: Refutation
% 0.21/0.53  
% 0.21/0.53  % (13941)Memory used [KB]: 11513
% 0.21/0.53  % (13941)Time elapsed: 0.109 s
% 0.21/0.53  % (13941)------------------------------
% 0.21/0.53  % (13941)------------------------------
% 0.21/0.53  % (13924)Success in time 0.172 s
%------------------------------------------------------------------------------
