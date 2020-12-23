%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:04 EST 2020

% Result     : Theorem 9.33s
% Output     : Refutation 9.33s
% Verified   : 
% Statistics : Number of formulae       :  193 ( 561 expanded)
%              Number of leaves         :   47 ( 270 expanded)
%              Depth                    :   10
%              Number of atoms          :  822 (2967 expanded)
%              Number of equality atoms :   20 (  39 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f23824,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f96,f101,f106,f111,f116,f121,f126,f131,f170,f186,f219,f437,f462,f477,f584,f589,f594,f647,f741,f879,f915,f980,f1085,f1090,f1095,f1100,f2958,f6805,f23821])).

fof(f23821,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | spl6_5
    | spl6_7
    | spl6_9
    | ~ spl6_15
    | ~ spl6_84
    | ~ spl6_121
    | ~ spl6_131
    | spl6_147
    | ~ spl6_148
    | ~ spl6_149
    | spl6_371
    | ~ spl6_884 ),
    inference(avatar_contradiction_clause,[],[f23820])).

fof(f23820,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_3
    | spl6_5
    | spl6_7
    | spl6_9
    | ~ spl6_15
    | ~ spl6_84
    | ~ spl6_121
    | ~ spl6_131
    | spl6_147
    | ~ spl6_148
    | ~ spl6_149
    | spl6_371
    | ~ spl6_884 ),
    inference(subsumption_resolution,[],[f23811,f6804])).

fof(f6804,plain,
    ( m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),k1_tsep_1(sK2,sK4,sK4))
    | ~ spl6_884 ),
    inference(avatar_component_clause,[],[f6802])).

fof(f6802,plain,
    ( spl6_884
  <=> m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),k1_tsep_1(sK2,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_884])])).

fof(f23811,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),k1_tsep_1(sK2,sK4,sK4))
    | ~ spl6_2
    | ~ spl6_3
    | spl6_5
    | spl6_7
    | spl6_9
    | ~ spl6_15
    | ~ spl6_84
    | ~ spl6_121
    | ~ spl6_131
    | spl6_147
    | ~ spl6_148
    | ~ spl6_149
    | spl6_371 ),
    inference(unit_resulting_resolution,[],[f105,f158,f115,f95,f646,f878,f979,f85,f80,f1084,f1089,f1094,f1094,f2945,f1278])).

fof(f1278,plain,(
    ! [X43,X41,X44,X42,X40] :
      ( r1_tarski(k2_xboole_0(u1_struct_0(X41),u1_struct_0(X42)),u1_struct_0(X43))
      | ~ m1_pre_topc(k1_tsep_1(X40,X41,X42),X43)
      | ~ m1_pre_topc(X43,X44)
      | ~ m1_pre_topc(k1_tsep_1(X40,X41,X42),X44)
      | ~ l1_pre_topc(X44)
      | ~ v2_pre_topc(X44)
      | ~ m1_pre_topc(k1_tsep_1(X40,X41,X42),X40)
      | ~ v1_pre_topc(k1_tsep_1(X40,X41,X42))
      | v2_struct_0(k1_tsep_1(X40,X41,X42))
      | ~ m1_pre_topc(X42,X40)
      | v2_struct_0(X42)
      | ~ m1_pre_topc(X41,X40)
      | v2_struct_0(X41)
      | ~ l1_pre_topc(X40)
      | v2_struct_0(X40) ) ),
    inference(superposition,[],[f62,f71])).

fof(f71,plain,(
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
    inference(equality_resolution,[],[f59])).

fof(f59,plain,(
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
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(nnf_transformation,[],[f19])).

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
             => ! [X3] :
                  ( ( m1_pre_topc(X3,X0)
                    & v1_pre_topc(X3)
                    & ~ v2_struct_0(X3) )
                 => ( k1_tsep_1(X0,X1,X2) = X3
                  <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
                  | ~ m1_pre_topc(X1,X2) )
                & ( m1_pre_topc(X1,X2)
                  | ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) ) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f2945,plain,
    ( ~ r1_tarski(k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5)),u1_struct_0(sK4))
    | spl6_371 ),
    inference(avatar_component_clause,[],[f2943])).

fof(f2943,plain,
    ( spl6_371
  <=> r1_tarski(k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5)),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_371])])).

fof(f1094,plain,
    ( m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),sK4)
    | ~ spl6_149 ),
    inference(avatar_component_clause,[],[f1092])).

fof(f1092,plain,
    ( spl6_149
  <=> m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_149])])).

fof(f1089,plain,
    ( v1_pre_topc(k1_tsep_1(sK4,sK3,sK5))
    | ~ spl6_148 ),
    inference(avatar_component_clause,[],[f1087])).

fof(f1087,plain,
    ( spl6_148
  <=> v1_pre_topc(k1_tsep_1(sK4,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_148])])).

fof(f1084,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK4,sK3,sK5))
    | spl6_147 ),
    inference(avatar_component_clause,[],[f1082])).

fof(f1082,plain,
    ( spl6_147
  <=> v2_struct_0(k1_tsep_1(sK4,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_147])])).

fof(f80,plain,
    ( m1_pre_topc(sK5,sK4)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f78])).

fof(f78,plain,
    ( spl6_2
  <=> m1_pre_topc(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f85,plain,
    ( m1_pre_topc(sK3,sK4)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f83])).

fof(f83,plain,
    ( spl6_3
  <=> m1_pre_topc(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f979,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK2,sK4,sK4))
    | ~ spl6_131 ),
    inference(avatar_component_clause,[],[f977])).

fof(f977,plain,
    ( spl6_131
  <=> m1_pre_topc(sK4,k1_tsep_1(sK2,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_131])])).

fof(f878,plain,
    ( v2_pre_topc(k1_tsep_1(sK2,sK4,sK4))
    | ~ spl6_121 ),
    inference(avatar_component_clause,[],[f876])).

fof(f876,plain,
    ( spl6_121
  <=> v2_pre_topc(k1_tsep_1(sK2,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_121])])).

fof(f646,plain,
    ( l1_pre_topc(k1_tsep_1(sK2,sK4,sK4))
    | ~ spl6_84 ),
    inference(avatar_component_clause,[],[f644])).

fof(f644,plain,
    ( spl6_84
  <=> l1_pre_topc(k1_tsep_1(sK2,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).

fof(f95,plain,
    ( ~ v2_struct_0(sK5)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f93,plain,
    ( spl6_5
  <=> v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f115,plain,
    ( ~ v2_struct_0(sK3)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f113])).

fof(f113,plain,
    ( spl6_9
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f158,plain,
    ( l1_pre_topc(sK4)
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f156])).

fof(f156,plain,
    ( spl6_15
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f105,plain,
    ( ~ v2_struct_0(sK4)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl6_7
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f6805,plain,
    ( spl6_884
    | ~ spl6_6
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | spl6_12
    | ~ spl6_149
    | ~ spl6_150 ),
    inference(avatar_split_clause,[],[f6799,f1097,f1092,f128,f123,f118,f103,f98,f6802])).

fof(f98,plain,
    ( spl6_6
  <=> m1_pre_topc(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f118,plain,
    ( spl6_10
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f123,plain,
    ( spl6_11
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f128,plain,
    ( spl6_12
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f1097,plain,
    ( spl6_150
  <=> l1_pre_topc(k1_tsep_1(sK4,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_150])])).

fof(f6799,plain,
    ( m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),k1_tsep_1(sK2,sK4,sK4))
    | ~ spl6_6
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | spl6_12
    | ~ spl6_149
    | ~ spl6_150 ),
    inference(unit_resulting_resolution,[],[f130,f125,f120,f105,f100,f1099,f1094,f928])).

fof(f928,plain,(
    ! [X6,X7,X5] :
      ( m1_pre_topc(X7,k1_tsep_1(X6,X5,X5))
      | ~ m1_pre_topc(X7,X5)
      | ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(X5,X6)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(subsumption_resolution,[],[f887,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f887,plain,(
    ! [X6,X7,X5] :
      ( m1_pre_topc(X7,k1_tsep_1(X6,X5,X5))
      | ~ m1_pre_topc(X7,X5)
      | ~ l1_pre_topc(X5)
      | ~ l1_pre_topc(X7)
      | ~ m1_pre_topc(X5,X6)
      | v2_struct_0(X5)
      | ~ l1_pre_topc(X6)
      | ~ v2_pre_topc(X6)
      | v2_struct_0(X6) ) ),
    inference(superposition,[],[f55,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f1099,plain,
    ( l1_pre_topc(k1_tsep_1(sK4,sK3,sK5))
    | ~ spl6_150 ),
    inference(avatar_component_clause,[],[f1097])).

fof(f100,plain,
    ( m1_pre_topc(sK4,sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f98])).

fof(f120,plain,
    ( l1_pre_topc(sK2)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f118])).

fof(f125,plain,
    ( v2_pre_topc(sK2)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f123])).

fof(f130,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f128])).

fof(f2958,plain,
    ( ~ spl6_371
    | spl6_1
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | spl6_12
    | spl6_73
    | ~ spl6_74
    | ~ spl6_75 ),
    inference(avatar_split_clause,[],[f2714,f591,f586,f581,f128,f123,f118,f113,f108,f98,f93,f88,f73,f2943])).

fof(f73,plain,
    ( spl6_1
  <=> m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f88,plain,
    ( spl6_4
  <=> m1_pre_topc(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f108,plain,
    ( spl6_8
  <=> m1_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f581,plain,
    ( spl6_73
  <=> v2_struct_0(k1_tsep_1(sK2,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).

fof(f586,plain,
    ( spl6_74
  <=> v1_pre_topc(k1_tsep_1(sK2,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).

fof(f591,plain,
    ( spl6_75
  <=> m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).

fof(f2714,plain,
    ( ~ r1_tarski(k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5)),u1_struct_0(sK4))
    | spl6_1
    | ~ spl6_4
    | spl6_5
    | ~ spl6_6
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | ~ spl6_11
    | spl6_12
    | spl6_73
    | ~ spl6_74
    | ~ spl6_75 ),
    inference(unit_resulting_resolution,[],[f130,f120,f115,f125,f95,f120,f110,f90,f100,f583,f588,f75,f593,f593,f1276])).

fof(f1276,plain,(
    ! [X30,X33,X31,X34,X32] :
      ( ~ r1_tarski(k2_xboole_0(u1_struct_0(X31),u1_struct_0(X32)),u1_struct_0(X33))
      | m1_pre_topc(k1_tsep_1(X30,X31,X32),X33)
      | ~ m1_pre_topc(X33,X34)
      | ~ m1_pre_topc(k1_tsep_1(X30,X31,X32),X34)
      | ~ l1_pre_topc(X34)
      | ~ v2_pre_topc(X34)
      | ~ m1_pre_topc(k1_tsep_1(X30,X31,X32),X30)
      | ~ v1_pre_topc(k1_tsep_1(X30,X31,X32))
      | v2_struct_0(k1_tsep_1(X30,X31,X32))
      | ~ m1_pre_topc(X32,X30)
      | v2_struct_0(X32)
      | ~ m1_pre_topc(X31,X30)
      | v2_struct_0(X31)
      | ~ l1_pre_topc(X30)
      | v2_struct_0(X30) ) ),
    inference(superposition,[],[f61,f71])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f593,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK2)
    | ~ spl6_75 ),
    inference(avatar_component_clause,[],[f591])).

fof(f75,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK4)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f73])).

fof(f588,plain,
    ( v1_pre_topc(k1_tsep_1(sK2,sK3,sK5))
    | ~ spl6_74 ),
    inference(avatar_component_clause,[],[f586])).

fof(f583,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK2,sK3,sK5))
    | spl6_73 ),
    inference(avatar_component_clause,[],[f581])).

fof(f90,plain,
    ( m1_pre_topc(sK5,sK2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f88])).

fof(f110,plain,
    ( m1_pre_topc(sK3,sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f108])).

fof(f1100,plain,
    ( spl6_150
    | ~ spl6_15
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f1077,f434,f156,f1097])).

fof(f434,plain,
    ( spl6_46
  <=> sP1(sK4,sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f1077,plain,
    ( l1_pre_topc(k1_tsep_1(sK4,sK3,sK5))
    | ~ spl6_15
    | ~ spl6_46 ),
    inference(unit_resulting_resolution,[],[f158,f436,f199])).

fof(f199,plain,(
    ! [X2,X0,X1] :
      ( l1_pre_topc(k1_tsep_1(X0,X2,X1))
      | ~ sP1(X0,X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f69,f57])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
        & v1_pre_topc(k1_tsep_1(X0,X2,X1))
        & ~ v2_struct_0(k1_tsep_1(X0,X2,X1)) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f40])).

fof(f40,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f436,plain,
    ( sP1(sK4,sK5,sK3)
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f434])).

fof(f1095,plain,
    ( spl6_149
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f1078,f434,f1092])).

fof(f1078,plain,
    ( m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),sK4)
    | ~ spl6_46 ),
    inference(unit_resulting_resolution,[],[f436,f69])).

fof(f1090,plain,
    ( spl6_148
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f1079,f434,f1087])).

fof(f1079,plain,
    ( v1_pre_topc(k1_tsep_1(sK4,sK3,sK5))
    | ~ spl6_46 ),
    inference(unit_resulting_resolution,[],[f436,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X2,X1))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f1085,plain,
    ( ~ spl6_147
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f1080,f434,f1082])).

fof(f1080,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK4,sK3,sK5))
    | ~ spl6_46 ),
    inference(unit_resulting_resolution,[],[f436,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X2,X1))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f980,plain,
    ( spl6_131
    | ~ spl6_21
    | ~ spl6_123 ),
    inference(avatar_split_clause,[],[f973,f912,f216,f977])).

fof(f216,plain,
    ( spl6_21
  <=> m1_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).

fof(f912,plain,
    ( spl6_123
  <=> g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k1_tsep_1(sK2,sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_123])])).

fof(f973,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK2,sK4,sK4))
    | ~ spl6_21
    | ~ spl6_123 ),
    inference(backward_demodulation,[],[f218,f914])).

fof(f914,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k1_tsep_1(sK2,sK4,sK4)
    | ~ spl6_123 ),
    inference(avatar_component_clause,[],[f912])).

fof(f218,plain,
    ( m1_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl6_21 ),
    inference(avatar_component_clause,[],[f216])).

fof(f915,plain,
    ( spl6_123
    | ~ spl6_6
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | spl6_12 ),
    inference(avatar_split_clause,[],[f882,f128,f123,f118,f103,f98,f912])).

fof(f882,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k1_tsep_1(sK2,sK4,sK4)
    | ~ spl6_6
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | spl6_12 ),
    inference(unit_resulting_resolution,[],[f130,f125,f120,f105,f100,f58])).

fof(f879,plain,
    ( spl6_121
    | ~ spl6_98 ),
    inference(avatar_split_clause,[],[f872,f738,f876])).

fof(f738,plain,
    ( spl6_98
  <=> sP0(sK4,sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).

fof(f872,plain,
    ( v2_pre_topc(k1_tsep_1(sK2,sK4,sK4))
    | ~ spl6_98 ),
    inference(unit_resulting_resolution,[],[f740,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v2_pre_topc(k1_tsep_1(X2,X1,X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( v2_pre_topc(k1_tsep_1(X2,X1,X0))
        & v1_pre_topc(k1_tsep_1(X2,X1,X0))
        & ~ v2_struct_0(k1_tsep_1(X2,X1,X0)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f38])).

fof(f38,plain,(
    ! [X2,X1,X0] :
      ( ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP0(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X2,X1,X0] :
      ( ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP0(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f740,plain,
    ( sP0(sK4,sK4,sK2)
    | ~ spl6_98 ),
    inference(avatar_component_clause,[],[f738])).

fof(f741,plain,
    ( spl6_98
    | ~ spl6_6
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | spl6_12 ),
    inference(avatar_split_clause,[],[f706,f128,f123,f118,f103,f98,f738])).

fof(f706,plain,
    ( sP0(sK4,sK4,sK2)
    | ~ spl6_6
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | spl6_12 ),
    inference(unit_resulting_resolution,[],[f130,f125,f120,f105,f100,f105,f100,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( sP0(X2,X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f23,f26])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(X2,X0)
        & ~ v2_struct_0(X2)
        & m1_pre_topc(X1,X0)
        & ~ v2_struct_0(X1)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tmap_1)).

fof(f647,plain,
    ( spl6_84
    | ~ spl6_10
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f624,f474,f118,f644])).

fof(f474,plain,
    ( spl6_54
  <=> sP1(sK2,sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f624,plain,
    ( l1_pre_topc(k1_tsep_1(sK2,sK4,sK4))
    | ~ spl6_10
    | ~ spl6_54 ),
    inference(unit_resulting_resolution,[],[f120,f476,f199])).

fof(f476,plain,
    ( sP1(sK2,sK4,sK4)
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f474])).

fof(f594,plain,
    ( spl6_75
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f577,f459,f591])).

fof(f459,plain,
    ( spl6_51
  <=> sP1(sK2,sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).

fof(f577,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK2)
    | ~ spl6_51 ),
    inference(unit_resulting_resolution,[],[f461,f69])).

fof(f461,plain,
    ( sP1(sK2,sK5,sK3)
    | ~ spl6_51 ),
    inference(avatar_component_clause,[],[f459])).

fof(f589,plain,
    ( spl6_74
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f578,f459,f586])).

fof(f578,plain,
    ( v1_pre_topc(k1_tsep_1(sK2,sK3,sK5))
    | ~ spl6_51 ),
    inference(unit_resulting_resolution,[],[f461,f68])).

fof(f584,plain,
    ( ~ spl6_73
    | ~ spl6_51 ),
    inference(avatar_split_clause,[],[f579,f459,f581])).

fof(f579,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK2,sK3,sK5))
    | ~ spl6_51 ),
    inference(unit_resulting_resolution,[],[f461,f67])).

fof(f477,plain,
    ( spl6_54
    | ~ spl6_6
    | spl6_7
    | ~ spl6_10
    | spl6_12 ),
    inference(avatar_split_clause,[],[f376,f128,f118,f103,f98,f474])).

fof(f376,plain,
    ( sP1(sK2,sK4,sK4)
    | ~ spl6_6
    | spl6_7
    | ~ spl6_10
    | spl6_12 ),
    inference(unit_resulting_resolution,[],[f130,f120,f105,f100,f105,f100,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f25,f28])).

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f462,plain,
    ( spl6_51
    | ~ spl6_4
    | spl6_5
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_12 ),
    inference(avatar_split_clause,[],[f379,f128,f118,f113,f108,f93,f88,f459])).

fof(f379,plain,
    ( sP1(sK2,sK5,sK3)
    | ~ spl6_4
    | spl6_5
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_12 ),
    inference(unit_resulting_resolution,[],[f130,f120,f115,f110,f95,f90,f70])).

fof(f437,plain,
    ( spl6_46
    | ~ spl6_2
    | ~ spl6_3
    | spl6_5
    | spl6_7
    | spl6_9
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f384,f156,f113,f103,f93,f83,f78,f434])).

fof(f384,plain,
    ( sP1(sK4,sK5,sK3)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_5
    | spl6_7
    | spl6_9
    | ~ spl6_15 ),
    inference(unit_resulting_resolution,[],[f105,f158,f115,f85,f95,f80,f70])).

fof(f219,plain,
    ( spl6_21
    | ~ spl6_15
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f207,f183,f156,f216])).

fof(f183,plain,
    ( spl6_18
  <=> m1_pre_topc(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f207,plain,
    ( m1_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl6_15
    | ~ spl6_18 ),
    inference(unit_resulting_resolution,[],[f158,f158,f185,f55])).

fof(f185,plain,
    ( m1_pre_topc(sK4,sK4)
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f183])).

fof(f186,plain,
    ( spl6_18
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f181,f156,f183])).

fof(f181,plain,
    ( m1_pre_topc(sK4,sK4)
    | ~ spl6_15 ),
    inference(unit_resulting_resolution,[],[f158,f54])).

fof(f54,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f170,plain,
    ( spl6_15
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f169,f118,f98,f156])).

fof(f169,plain,
    ( l1_pre_topc(sK4)
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f146,f120])).

fof(f146,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ spl6_6 ),
    inference(resolution,[],[f57,f100])).

fof(f131,plain,(
    ~ spl6_12 ),
    inference(avatar_split_clause,[],[f42,f128])).

fof(f42,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK4)
    & m1_pre_topc(sK5,sK4)
    & m1_pre_topc(sK3,sK4)
    & m1_pre_topc(sK5,sK2)
    & ~ v2_struct_0(sK5)
    & m1_pre_topc(sK4,sK2)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK2)
    & ~ v2_struct_0(sK3)
    & l1_pre_topc(sK2)
    & v2_pre_topc(sK2)
    & ~ v2_struct_0(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f12,f33,f32,f31,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                    & m1_pre_topc(X3,X2)
                    & m1_pre_topc(X1,X2)
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
                  ( ~ m1_pre_topc(k1_tsep_1(sK2,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
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

fof(f31,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_pre_topc(k1_tsep_1(sK2,X1,X3),X2)
                & m1_pre_topc(X3,X2)
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK2)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK2)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK2)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_pre_topc(k1_tsep_1(sK2,sK3,X3),X2)
              & m1_pre_topc(X3,X2)
              & m1_pre_topc(sK3,X2)
              & m1_pre_topc(X3,sK2)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK2)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK3,sK2)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_pre_topc(k1_tsep_1(sK2,sK3,X3),X2)
            & m1_pre_topc(X3,X2)
            & m1_pre_topc(sK3,X2)
            & m1_pre_topc(X3,sK2)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK2)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ m1_pre_topc(k1_tsep_1(sK2,sK3,X3),sK4)
          & m1_pre_topc(X3,sK4)
          & m1_pre_topc(sK3,sK4)
          & m1_pre_topc(X3,sK2)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK4,sK2)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X3] :
        ( ~ m1_pre_topc(k1_tsep_1(sK2,sK3,X3),sK4)
        & m1_pre_topc(X3,sK4)
        & m1_pre_topc(sK3,sK4)
        & m1_pre_topc(X3,sK2)
        & ~ v2_struct_0(X3) )
   => ( ~ m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK4)
      & m1_pre_topc(sK5,sK4)
      & m1_pre_topc(sK3,sK4)
      & m1_pre_topc(sK5,sK2)
      & ~ v2_struct_0(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
                   => ( ( m1_pre_topc(X3,X2)
                        & m1_pre_topc(X1,X2) )
                     => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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
                 => ( ( m1_pre_topc(X3,X2)
                      & m1_pre_topc(X1,X2) )
                   => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tmap_1)).

fof(f126,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f43,f123])).

fof(f43,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f121,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f44,f118])).

fof(f44,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f116,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f45,f113])).

fof(f45,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f34])).

fof(f111,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f46,f108])).

fof(f46,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f106,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f47,f103])).

fof(f47,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f101,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f48,f98])).

fof(f48,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f96,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f49,f93])).

fof(f49,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f34])).

fof(f91,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f50,f88])).

fof(f50,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f86,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f51,f83])).

fof(f51,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f81,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f52,f78])).

fof(f52,plain,(
    m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f34])).

fof(f76,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f53,f73])).

fof(f53,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK4) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:00:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (21265)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.47  % (21259)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (21260)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (21257)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.48  % (21268)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (21267)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (21273)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.49  % (21269)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (21266)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (21256)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (21255)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (21261)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (21255)Refutation not found, incomplete strategy% (21255)------------------------------
% 0.21/0.50  % (21255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (21255)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (21255)Memory used [KB]: 10618
% 0.21/0.50  % (21255)Time elapsed: 0.087 s
% 0.21/0.50  % (21255)------------------------------
% 0.21/0.50  % (21255)------------------------------
% 0.21/0.50  % (21254)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (21272)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (21271)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  % (21258)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (21264)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.51  % (21264)Refutation not found, incomplete strategy% (21264)------------------------------
% 0.21/0.51  % (21264)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (21264)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (21264)Memory used [KB]: 6140
% 0.21/0.51  % (21264)Time elapsed: 0.096 s
% 0.21/0.51  % (21264)------------------------------
% 0.21/0.51  % (21264)------------------------------
% 0.21/0.51  % (21263)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  % (21274)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.52  % (21262)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.52  % (21270)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.53  % (21274)Refutation not found, incomplete strategy% (21274)------------------------------
% 0.21/0.53  % (21274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (21274)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (21274)Memory used [KB]: 10618
% 0.21/0.53  % (21274)Time elapsed: 0.117 s
% 0.21/0.53  % (21274)------------------------------
% 0.21/0.53  % (21274)------------------------------
% 4.28/0.92  % (21259)Time limit reached!
% 4.28/0.92  % (21259)------------------------------
% 4.28/0.92  % (21259)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.28/0.92  % (21259)Termination reason: Time limit
% 4.28/0.92  
% 4.28/0.92  % (21259)Memory used [KB]: 8187
% 4.28/0.92  % (21259)Time elapsed: 0.502 s
% 4.28/0.92  % (21259)------------------------------
% 4.28/0.92  % (21259)------------------------------
% 4.51/0.92  % (21254)Time limit reached!
% 4.51/0.92  % (21254)------------------------------
% 4.51/0.92  % (21254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.51/0.92  % (21254)Termination reason: Time limit
% 4.51/0.92  
% 4.51/0.92  % (21254)Memory used [KB]: 10746
% 4.51/0.92  % (21254)Time elapsed: 0.516 s
% 4.51/0.92  % (21254)------------------------------
% 4.51/0.92  % (21254)------------------------------
% 4.51/0.93  % (21266)Time limit reached!
% 4.51/0.93  % (21266)------------------------------
% 4.51/0.93  % (21266)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 4.51/0.93  % (21266)Termination reason: Time limit
% 4.51/0.93  
% 4.51/0.93  % (21266)Memory used [KB]: 17910
% 4.51/0.93  % (21266)Time elapsed: 0.516 s
% 4.51/0.93  % (21266)------------------------------
% 4.51/0.93  % (21266)------------------------------
% 5.31/1.03  % (21262)Time limit reached!
% 5.31/1.03  % (21262)------------------------------
% 5.31/1.03  % (21262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.31/1.05  % (21262)Termination reason: Time limit
% 5.31/1.05  
% 5.31/1.05  % (21262)Memory used [KB]: 8571
% 5.31/1.05  % (21262)Time elapsed: 0.631 s
% 5.31/1.05  % (21262)------------------------------
% 5.31/1.05  % (21262)------------------------------
% 7.64/1.34  % (21263)Time limit reached!
% 7.64/1.34  % (21263)------------------------------
% 7.64/1.34  % (21263)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 7.64/1.35  % (21263)Termination reason: Time limit
% 7.64/1.35  
% 7.64/1.35  % (21263)Memory used [KB]: 22131
% 7.64/1.35  % (21263)Time elapsed: 0.928 s
% 7.64/1.35  % (21263)------------------------------
% 7.64/1.35  % (21263)------------------------------
% 9.21/1.52  % (21256)Time limit reached!
% 9.21/1.52  % (21256)------------------------------
% 9.21/1.52  % (21256)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.21/1.52  % (21256)Termination reason: Time limit
% 9.21/1.52  % (21256)Termination phase: Saturation
% 9.21/1.52  
% 9.21/1.52  % (21256)Memory used [KB]: 20980
% 9.21/1.52  % (21256)Time elapsed: 1.100 s
% 9.21/1.52  % (21256)------------------------------
% 9.21/1.52  % (21256)------------------------------
% 9.33/1.58  % (21270)Refutation found. Thanks to Tanya!
% 9.33/1.58  % SZS status Theorem for theBenchmark
% 9.33/1.58  % SZS output start Proof for theBenchmark
% 9.33/1.58  fof(f23824,plain,(
% 9.33/1.58    $false),
% 9.33/1.58    inference(avatar_sat_refutation,[],[f76,f81,f86,f91,f96,f101,f106,f111,f116,f121,f126,f131,f170,f186,f219,f437,f462,f477,f584,f589,f594,f647,f741,f879,f915,f980,f1085,f1090,f1095,f1100,f2958,f6805,f23821])).
% 9.33/1.58  fof(f23821,plain,(
% 9.33/1.58    ~spl6_2 | ~spl6_3 | spl6_5 | spl6_7 | spl6_9 | ~spl6_15 | ~spl6_84 | ~spl6_121 | ~spl6_131 | spl6_147 | ~spl6_148 | ~spl6_149 | spl6_371 | ~spl6_884),
% 9.33/1.58    inference(avatar_contradiction_clause,[],[f23820])).
% 9.33/1.58  fof(f23820,plain,(
% 9.33/1.58    $false | (~spl6_2 | ~spl6_3 | spl6_5 | spl6_7 | spl6_9 | ~spl6_15 | ~spl6_84 | ~spl6_121 | ~spl6_131 | spl6_147 | ~spl6_148 | ~spl6_149 | spl6_371 | ~spl6_884)),
% 9.33/1.58    inference(subsumption_resolution,[],[f23811,f6804])).
% 9.33/1.58  fof(f6804,plain,(
% 9.33/1.58    m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),k1_tsep_1(sK2,sK4,sK4)) | ~spl6_884),
% 9.33/1.58    inference(avatar_component_clause,[],[f6802])).
% 9.33/1.58  fof(f6802,plain,(
% 9.33/1.58    spl6_884 <=> m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),k1_tsep_1(sK2,sK4,sK4))),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_884])])).
% 9.33/1.58  fof(f23811,plain,(
% 9.33/1.58    ~m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),k1_tsep_1(sK2,sK4,sK4)) | (~spl6_2 | ~spl6_3 | spl6_5 | spl6_7 | spl6_9 | ~spl6_15 | ~spl6_84 | ~spl6_121 | ~spl6_131 | spl6_147 | ~spl6_148 | ~spl6_149 | spl6_371)),
% 9.33/1.58    inference(unit_resulting_resolution,[],[f105,f158,f115,f95,f646,f878,f979,f85,f80,f1084,f1089,f1094,f1094,f2945,f1278])).
% 9.33/1.58  fof(f1278,plain,(
% 9.33/1.58    ( ! [X43,X41,X44,X42,X40] : (r1_tarski(k2_xboole_0(u1_struct_0(X41),u1_struct_0(X42)),u1_struct_0(X43)) | ~m1_pre_topc(k1_tsep_1(X40,X41,X42),X43) | ~m1_pre_topc(X43,X44) | ~m1_pre_topc(k1_tsep_1(X40,X41,X42),X44) | ~l1_pre_topc(X44) | ~v2_pre_topc(X44) | ~m1_pre_topc(k1_tsep_1(X40,X41,X42),X40) | ~v1_pre_topc(k1_tsep_1(X40,X41,X42)) | v2_struct_0(k1_tsep_1(X40,X41,X42)) | ~m1_pre_topc(X42,X40) | v2_struct_0(X42) | ~m1_pre_topc(X41,X40) | v2_struct_0(X41) | ~l1_pre_topc(X40) | v2_struct_0(X40)) )),
% 9.33/1.58    inference(superposition,[],[f62,f71])).
% 9.33/1.58  fof(f71,plain,(
% 9.33/1.58    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 9.33/1.58    inference(equality_resolution,[],[f59])).
% 9.33/1.58  fof(f59,plain,(
% 9.33/1.58    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 9.33/1.58    inference(cnf_transformation,[],[f36])).
% 9.33/1.58  fof(f36,plain,(
% 9.33/1.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 9.33/1.58    inference(nnf_transformation,[],[f19])).
% 9.33/1.58  fof(f19,plain,(
% 9.33/1.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 9.33/1.58    inference(flattening,[],[f18])).
% 9.33/1.58  fof(f18,plain,(
% 9.33/1.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 9.33/1.58    inference(ennf_transformation,[],[f3])).
% 9.33/1.58  fof(f3,axiom,(
% 9.33/1.58    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 9.33/1.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).
% 9.33/1.58  fof(f62,plain,(
% 9.33/1.58    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 9.33/1.58    inference(cnf_transformation,[],[f37])).
% 9.33/1.58  fof(f37,plain,(
% 9.33/1.58    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 9.33/1.58    inference(nnf_transformation,[],[f21])).
% 9.33/1.58  fof(f21,plain,(
% 9.33/1.58    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 9.33/1.58    inference(flattening,[],[f20])).
% 9.33/1.58  fof(f20,plain,(
% 9.33/1.58    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 9.33/1.58    inference(ennf_transformation,[],[f8])).
% 9.33/1.58  fof(f8,axiom,(
% 9.33/1.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 9.33/1.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 9.33/1.58  fof(f2945,plain,(
% 9.33/1.58    ~r1_tarski(k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5)),u1_struct_0(sK4)) | spl6_371),
% 9.33/1.58    inference(avatar_component_clause,[],[f2943])).
% 9.33/1.58  fof(f2943,plain,(
% 9.33/1.58    spl6_371 <=> r1_tarski(k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5)),u1_struct_0(sK4))),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_371])])).
% 9.33/1.58  fof(f1094,plain,(
% 9.33/1.58    m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),sK4) | ~spl6_149),
% 9.33/1.58    inference(avatar_component_clause,[],[f1092])).
% 9.33/1.58  fof(f1092,plain,(
% 9.33/1.58    spl6_149 <=> m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),sK4)),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_149])])).
% 9.33/1.58  fof(f1089,plain,(
% 9.33/1.58    v1_pre_topc(k1_tsep_1(sK4,sK3,sK5)) | ~spl6_148),
% 9.33/1.58    inference(avatar_component_clause,[],[f1087])).
% 9.33/1.58  fof(f1087,plain,(
% 9.33/1.58    spl6_148 <=> v1_pre_topc(k1_tsep_1(sK4,sK3,sK5))),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_148])])).
% 9.33/1.58  fof(f1084,plain,(
% 9.33/1.58    ~v2_struct_0(k1_tsep_1(sK4,sK3,sK5)) | spl6_147),
% 9.33/1.58    inference(avatar_component_clause,[],[f1082])).
% 9.33/1.58  fof(f1082,plain,(
% 9.33/1.58    spl6_147 <=> v2_struct_0(k1_tsep_1(sK4,sK3,sK5))),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_147])])).
% 9.33/1.58  fof(f80,plain,(
% 9.33/1.58    m1_pre_topc(sK5,sK4) | ~spl6_2),
% 9.33/1.58    inference(avatar_component_clause,[],[f78])).
% 9.33/1.58  fof(f78,plain,(
% 9.33/1.58    spl6_2 <=> m1_pre_topc(sK5,sK4)),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 9.33/1.58  fof(f85,plain,(
% 9.33/1.58    m1_pre_topc(sK3,sK4) | ~spl6_3),
% 9.33/1.58    inference(avatar_component_clause,[],[f83])).
% 9.33/1.58  fof(f83,plain,(
% 9.33/1.58    spl6_3 <=> m1_pre_topc(sK3,sK4)),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 9.33/1.58  fof(f979,plain,(
% 9.33/1.58    m1_pre_topc(sK4,k1_tsep_1(sK2,sK4,sK4)) | ~spl6_131),
% 9.33/1.58    inference(avatar_component_clause,[],[f977])).
% 9.33/1.58  fof(f977,plain,(
% 9.33/1.58    spl6_131 <=> m1_pre_topc(sK4,k1_tsep_1(sK2,sK4,sK4))),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_131])])).
% 9.33/1.58  fof(f878,plain,(
% 9.33/1.58    v2_pre_topc(k1_tsep_1(sK2,sK4,sK4)) | ~spl6_121),
% 9.33/1.58    inference(avatar_component_clause,[],[f876])).
% 9.33/1.58  fof(f876,plain,(
% 9.33/1.58    spl6_121 <=> v2_pre_topc(k1_tsep_1(sK2,sK4,sK4))),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_121])])).
% 9.33/1.58  fof(f646,plain,(
% 9.33/1.58    l1_pre_topc(k1_tsep_1(sK2,sK4,sK4)) | ~spl6_84),
% 9.33/1.58    inference(avatar_component_clause,[],[f644])).
% 9.33/1.58  fof(f644,plain,(
% 9.33/1.58    spl6_84 <=> l1_pre_topc(k1_tsep_1(sK2,sK4,sK4))),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_84])])).
% 9.33/1.58  fof(f95,plain,(
% 9.33/1.58    ~v2_struct_0(sK5) | spl6_5),
% 9.33/1.58    inference(avatar_component_clause,[],[f93])).
% 9.33/1.58  fof(f93,plain,(
% 9.33/1.58    spl6_5 <=> v2_struct_0(sK5)),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 9.33/1.58  fof(f115,plain,(
% 9.33/1.58    ~v2_struct_0(sK3) | spl6_9),
% 9.33/1.58    inference(avatar_component_clause,[],[f113])).
% 9.33/1.58  fof(f113,plain,(
% 9.33/1.58    spl6_9 <=> v2_struct_0(sK3)),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 9.33/1.58  fof(f158,plain,(
% 9.33/1.58    l1_pre_topc(sK4) | ~spl6_15),
% 9.33/1.58    inference(avatar_component_clause,[],[f156])).
% 9.33/1.58  fof(f156,plain,(
% 9.33/1.58    spl6_15 <=> l1_pre_topc(sK4)),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 9.33/1.58  fof(f105,plain,(
% 9.33/1.58    ~v2_struct_0(sK4) | spl6_7),
% 9.33/1.58    inference(avatar_component_clause,[],[f103])).
% 9.33/1.58  fof(f103,plain,(
% 9.33/1.58    spl6_7 <=> v2_struct_0(sK4)),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 9.33/1.58  fof(f6805,plain,(
% 9.33/1.58    spl6_884 | ~spl6_6 | spl6_7 | ~spl6_10 | ~spl6_11 | spl6_12 | ~spl6_149 | ~spl6_150),
% 9.33/1.58    inference(avatar_split_clause,[],[f6799,f1097,f1092,f128,f123,f118,f103,f98,f6802])).
% 9.33/1.58  fof(f98,plain,(
% 9.33/1.58    spl6_6 <=> m1_pre_topc(sK4,sK2)),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 9.33/1.58  fof(f118,plain,(
% 9.33/1.58    spl6_10 <=> l1_pre_topc(sK2)),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 9.33/1.58  fof(f123,plain,(
% 9.33/1.58    spl6_11 <=> v2_pre_topc(sK2)),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 9.33/1.58  fof(f128,plain,(
% 9.33/1.58    spl6_12 <=> v2_struct_0(sK2)),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 9.33/1.58  fof(f1097,plain,(
% 9.33/1.58    spl6_150 <=> l1_pre_topc(k1_tsep_1(sK4,sK3,sK5))),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_150])])).
% 9.33/1.58  fof(f6799,plain,(
% 9.33/1.58    m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),k1_tsep_1(sK2,sK4,sK4)) | (~spl6_6 | spl6_7 | ~spl6_10 | ~spl6_11 | spl6_12 | ~spl6_149 | ~spl6_150)),
% 9.33/1.58    inference(unit_resulting_resolution,[],[f130,f125,f120,f105,f100,f1099,f1094,f928])).
% 9.33/1.58  fof(f928,plain,(
% 9.33/1.58    ( ! [X6,X7,X5] : (m1_pre_topc(X7,k1_tsep_1(X6,X5,X5)) | ~m1_pre_topc(X7,X5) | ~l1_pre_topc(X7) | ~m1_pre_topc(X5,X6) | v2_struct_0(X5) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 9.33/1.58    inference(subsumption_resolution,[],[f887,f57])).
% 9.33/1.58  fof(f57,plain,(
% 9.33/1.58    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 9.33/1.58    inference(cnf_transformation,[],[f15])).
% 9.33/1.58  fof(f15,plain,(
% 9.33/1.58    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 9.33/1.58    inference(ennf_transformation,[],[f1])).
% 9.33/1.58  fof(f1,axiom,(
% 9.33/1.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 9.33/1.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 9.33/1.58  fof(f887,plain,(
% 9.33/1.58    ( ! [X6,X7,X5] : (m1_pre_topc(X7,k1_tsep_1(X6,X5,X5)) | ~m1_pre_topc(X7,X5) | ~l1_pre_topc(X5) | ~l1_pre_topc(X7) | ~m1_pre_topc(X5,X6) | v2_struct_0(X5) | ~l1_pre_topc(X6) | ~v2_pre_topc(X6) | v2_struct_0(X6)) )),
% 9.33/1.58    inference(superposition,[],[f55,f58])).
% 9.33/1.58  fof(f58,plain,(
% 9.33/1.58    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 9.33/1.58    inference(cnf_transformation,[],[f17])).
% 9.33/1.58  fof(f17,plain,(
% 9.33/1.58    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 9.33/1.58    inference(flattening,[],[f16])).
% 9.33/1.58  fof(f16,plain,(
% 9.33/1.58    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 9.33/1.58    inference(ennf_transformation,[],[f6])).
% 9.33/1.58  fof(f6,axiom,(
% 9.33/1.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)))),
% 9.33/1.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).
% 9.33/1.58  fof(f55,plain,(
% 9.33/1.58    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 9.33/1.58    inference(cnf_transformation,[],[f35])).
% 9.33/1.58  fof(f35,plain,(
% 9.33/1.58    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 9.33/1.58    inference(nnf_transformation,[],[f14])).
% 9.33/1.58  fof(f14,plain,(
% 9.33/1.58    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 9.33/1.58    inference(ennf_transformation,[],[f2])).
% 9.33/1.58  fof(f2,axiom,(
% 9.33/1.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 9.33/1.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_pre_topc)).
% 9.33/1.58  fof(f1099,plain,(
% 9.33/1.58    l1_pre_topc(k1_tsep_1(sK4,sK3,sK5)) | ~spl6_150),
% 9.33/1.58    inference(avatar_component_clause,[],[f1097])).
% 9.33/1.58  fof(f100,plain,(
% 9.33/1.58    m1_pre_topc(sK4,sK2) | ~spl6_6),
% 9.33/1.58    inference(avatar_component_clause,[],[f98])).
% 9.33/1.58  fof(f120,plain,(
% 9.33/1.58    l1_pre_topc(sK2) | ~spl6_10),
% 9.33/1.58    inference(avatar_component_clause,[],[f118])).
% 9.33/1.58  fof(f125,plain,(
% 9.33/1.58    v2_pre_topc(sK2) | ~spl6_11),
% 9.33/1.58    inference(avatar_component_clause,[],[f123])).
% 9.33/1.58  fof(f130,plain,(
% 9.33/1.58    ~v2_struct_0(sK2) | spl6_12),
% 9.33/1.58    inference(avatar_component_clause,[],[f128])).
% 9.33/1.58  fof(f2958,plain,(
% 9.33/1.58    ~spl6_371 | spl6_1 | ~spl6_4 | spl6_5 | ~spl6_6 | ~spl6_8 | spl6_9 | ~spl6_10 | ~spl6_11 | spl6_12 | spl6_73 | ~spl6_74 | ~spl6_75),
% 9.33/1.58    inference(avatar_split_clause,[],[f2714,f591,f586,f581,f128,f123,f118,f113,f108,f98,f93,f88,f73,f2943])).
% 9.33/1.58  fof(f73,plain,(
% 9.33/1.58    spl6_1 <=> m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK4)),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 9.33/1.58  fof(f88,plain,(
% 9.33/1.58    spl6_4 <=> m1_pre_topc(sK5,sK2)),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 9.33/1.58  fof(f108,plain,(
% 9.33/1.58    spl6_8 <=> m1_pre_topc(sK3,sK2)),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 9.33/1.58  fof(f581,plain,(
% 9.33/1.58    spl6_73 <=> v2_struct_0(k1_tsep_1(sK2,sK3,sK5))),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_73])])).
% 9.33/1.58  fof(f586,plain,(
% 9.33/1.58    spl6_74 <=> v1_pre_topc(k1_tsep_1(sK2,sK3,sK5))),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_74])])).
% 9.33/1.58  fof(f591,plain,(
% 9.33/1.58    spl6_75 <=> m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK2)),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_75])])).
% 9.33/1.58  fof(f2714,plain,(
% 9.33/1.58    ~r1_tarski(k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5)),u1_struct_0(sK4)) | (spl6_1 | ~spl6_4 | spl6_5 | ~spl6_6 | ~spl6_8 | spl6_9 | ~spl6_10 | ~spl6_11 | spl6_12 | spl6_73 | ~spl6_74 | ~spl6_75)),
% 9.33/1.58    inference(unit_resulting_resolution,[],[f130,f120,f115,f125,f95,f120,f110,f90,f100,f583,f588,f75,f593,f593,f1276])).
% 9.33/1.58  fof(f1276,plain,(
% 9.33/1.58    ( ! [X30,X33,X31,X34,X32] : (~r1_tarski(k2_xboole_0(u1_struct_0(X31),u1_struct_0(X32)),u1_struct_0(X33)) | m1_pre_topc(k1_tsep_1(X30,X31,X32),X33) | ~m1_pre_topc(X33,X34) | ~m1_pre_topc(k1_tsep_1(X30,X31,X32),X34) | ~l1_pre_topc(X34) | ~v2_pre_topc(X34) | ~m1_pre_topc(k1_tsep_1(X30,X31,X32),X30) | ~v1_pre_topc(k1_tsep_1(X30,X31,X32)) | v2_struct_0(k1_tsep_1(X30,X31,X32)) | ~m1_pre_topc(X32,X30) | v2_struct_0(X32) | ~m1_pre_topc(X31,X30) | v2_struct_0(X31) | ~l1_pre_topc(X30) | v2_struct_0(X30)) )),
% 9.33/1.58    inference(superposition,[],[f61,f71])).
% 9.33/1.58  fof(f61,plain,(
% 9.33/1.58    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 9.33/1.58    inference(cnf_transformation,[],[f37])).
% 9.33/1.58  fof(f593,plain,(
% 9.33/1.58    m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK2) | ~spl6_75),
% 9.33/1.58    inference(avatar_component_clause,[],[f591])).
% 9.33/1.58  fof(f75,plain,(
% 9.33/1.58    ~m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK4) | spl6_1),
% 9.33/1.58    inference(avatar_component_clause,[],[f73])).
% 9.33/1.58  fof(f588,plain,(
% 9.33/1.58    v1_pre_topc(k1_tsep_1(sK2,sK3,sK5)) | ~spl6_74),
% 9.33/1.58    inference(avatar_component_clause,[],[f586])).
% 9.33/1.58  fof(f583,plain,(
% 9.33/1.58    ~v2_struct_0(k1_tsep_1(sK2,sK3,sK5)) | spl6_73),
% 9.33/1.58    inference(avatar_component_clause,[],[f581])).
% 9.33/1.58  fof(f90,plain,(
% 9.33/1.58    m1_pre_topc(sK5,sK2) | ~spl6_4),
% 9.33/1.58    inference(avatar_component_clause,[],[f88])).
% 9.33/1.58  fof(f110,plain,(
% 9.33/1.58    m1_pre_topc(sK3,sK2) | ~spl6_8),
% 9.33/1.58    inference(avatar_component_clause,[],[f108])).
% 9.33/1.58  fof(f1100,plain,(
% 9.33/1.58    spl6_150 | ~spl6_15 | ~spl6_46),
% 9.33/1.58    inference(avatar_split_clause,[],[f1077,f434,f156,f1097])).
% 9.33/1.58  fof(f434,plain,(
% 9.33/1.58    spl6_46 <=> sP1(sK4,sK5,sK3)),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 9.33/1.58  fof(f1077,plain,(
% 9.33/1.58    l1_pre_topc(k1_tsep_1(sK4,sK3,sK5)) | (~spl6_15 | ~spl6_46)),
% 9.33/1.58    inference(unit_resulting_resolution,[],[f158,f436,f199])).
% 9.33/1.58  fof(f199,plain,(
% 9.33/1.58    ( ! [X2,X0,X1] : (l1_pre_topc(k1_tsep_1(X0,X2,X1)) | ~sP1(X0,X1,X2) | ~l1_pre_topc(X0)) )),
% 9.33/1.58    inference(resolution,[],[f69,f57])).
% 9.33/1.58  fof(f69,plain,(
% 9.33/1.58    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X2,X1),X0) | ~sP1(X0,X1,X2)) )),
% 9.33/1.58    inference(cnf_transformation,[],[f41])).
% 9.33/1.58  fof(f41,plain,(
% 9.33/1.58    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X2,X1),X0) & v1_pre_topc(k1_tsep_1(X0,X2,X1)) & ~v2_struct_0(k1_tsep_1(X0,X2,X1))) | ~sP1(X0,X1,X2))),
% 9.33/1.58    inference(rectify,[],[f40])).
% 9.33/1.58  fof(f40,plain,(
% 9.33/1.58    ! [X0,X2,X1] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP1(X0,X2,X1))),
% 9.33/1.58    inference(nnf_transformation,[],[f28])).
% 9.33/1.58  fof(f28,plain,(
% 9.33/1.58    ! [X0,X2,X1] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP1(X0,X2,X1))),
% 9.33/1.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 9.33/1.58  fof(f436,plain,(
% 9.33/1.58    sP1(sK4,sK5,sK3) | ~spl6_46),
% 9.33/1.58    inference(avatar_component_clause,[],[f434])).
% 9.33/1.58  fof(f1095,plain,(
% 9.33/1.58    spl6_149 | ~spl6_46),
% 9.33/1.58    inference(avatar_split_clause,[],[f1078,f434,f1092])).
% 9.33/1.58  fof(f1078,plain,(
% 9.33/1.58    m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),sK4) | ~spl6_46),
% 9.33/1.58    inference(unit_resulting_resolution,[],[f436,f69])).
% 9.33/1.58  fof(f1090,plain,(
% 9.33/1.58    spl6_148 | ~spl6_46),
% 9.33/1.58    inference(avatar_split_clause,[],[f1079,f434,f1087])).
% 9.33/1.58  fof(f1079,plain,(
% 9.33/1.58    v1_pre_topc(k1_tsep_1(sK4,sK3,sK5)) | ~spl6_46),
% 9.33/1.58    inference(unit_resulting_resolution,[],[f436,f68])).
% 9.33/1.58  fof(f68,plain,(
% 9.33/1.58    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X2,X1)) | ~sP1(X0,X1,X2)) )),
% 9.33/1.58    inference(cnf_transformation,[],[f41])).
% 9.33/1.58  fof(f1085,plain,(
% 9.33/1.58    ~spl6_147 | ~spl6_46),
% 9.33/1.58    inference(avatar_split_clause,[],[f1080,f434,f1082])).
% 9.33/1.58  fof(f1080,plain,(
% 9.33/1.58    ~v2_struct_0(k1_tsep_1(sK4,sK3,sK5)) | ~spl6_46),
% 9.33/1.58    inference(unit_resulting_resolution,[],[f436,f67])).
% 9.33/1.58  fof(f67,plain,(
% 9.33/1.58    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X2,X1)) | ~sP1(X0,X1,X2)) )),
% 9.33/1.58    inference(cnf_transformation,[],[f41])).
% 9.33/1.58  fof(f980,plain,(
% 9.33/1.58    spl6_131 | ~spl6_21 | ~spl6_123),
% 9.33/1.58    inference(avatar_split_clause,[],[f973,f912,f216,f977])).
% 9.33/1.58  fof(f216,plain,(
% 9.33/1.58    spl6_21 <=> m1_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_21])])).
% 9.33/1.58  fof(f912,plain,(
% 9.33/1.58    spl6_123 <=> g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k1_tsep_1(sK2,sK4,sK4)),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_123])])).
% 9.33/1.58  fof(f973,plain,(
% 9.33/1.58    m1_pre_topc(sK4,k1_tsep_1(sK2,sK4,sK4)) | (~spl6_21 | ~spl6_123)),
% 9.33/1.58    inference(backward_demodulation,[],[f218,f914])).
% 9.33/1.58  fof(f914,plain,(
% 9.33/1.58    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k1_tsep_1(sK2,sK4,sK4) | ~spl6_123),
% 9.33/1.58    inference(avatar_component_clause,[],[f912])).
% 9.33/1.58  fof(f218,plain,(
% 9.33/1.58    m1_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | ~spl6_21),
% 9.33/1.58    inference(avatar_component_clause,[],[f216])).
% 9.33/1.58  fof(f915,plain,(
% 9.33/1.58    spl6_123 | ~spl6_6 | spl6_7 | ~spl6_10 | ~spl6_11 | spl6_12),
% 9.33/1.58    inference(avatar_split_clause,[],[f882,f128,f123,f118,f103,f98,f912])).
% 9.33/1.58  fof(f882,plain,(
% 9.33/1.58    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k1_tsep_1(sK2,sK4,sK4) | (~spl6_6 | spl6_7 | ~spl6_10 | ~spl6_11 | spl6_12)),
% 9.33/1.58    inference(unit_resulting_resolution,[],[f130,f125,f120,f105,f100,f58])).
% 9.33/1.58  fof(f879,plain,(
% 9.33/1.58    spl6_121 | ~spl6_98),
% 9.33/1.58    inference(avatar_split_clause,[],[f872,f738,f876])).
% 9.33/1.58  fof(f738,plain,(
% 9.33/1.58    spl6_98 <=> sP0(sK4,sK4,sK2)),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).
% 9.33/1.58  fof(f872,plain,(
% 9.33/1.58    v2_pre_topc(k1_tsep_1(sK2,sK4,sK4)) | ~spl6_98),
% 9.33/1.58    inference(unit_resulting_resolution,[],[f740,f65])).
% 9.33/1.58  fof(f65,plain,(
% 9.33/1.58    ( ! [X2,X0,X1] : (v2_pre_topc(k1_tsep_1(X2,X1,X0)) | ~sP0(X0,X1,X2)) )),
% 9.33/1.58    inference(cnf_transformation,[],[f39])).
% 9.33/1.58  fof(f39,plain,(
% 9.33/1.58    ! [X0,X1,X2] : ((v2_pre_topc(k1_tsep_1(X2,X1,X0)) & v1_pre_topc(k1_tsep_1(X2,X1,X0)) & ~v2_struct_0(k1_tsep_1(X2,X1,X0))) | ~sP0(X0,X1,X2))),
% 9.33/1.58    inference(rectify,[],[f38])).
% 9.33/1.58  fof(f38,plain,(
% 9.33/1.58    ! [X2,X1,X0] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP0(X2,X1,X0))),
% 9.33/1.58    inference(nnf_transformation,[],[f26])).
% 9.33/1.58  fof(f26,plain,(
% 9.33/1.58    ! [X2,X1,X0] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP0(X2,X1,X0))),
% 9.33/1.58    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 9.33/1.58  fof(f740,plain,(
% 9.33/1.58    sP0(sK4,sK4,sK2) | ~spl6_98),
% 9.33/1.58    inference(avatar_component_clause,[],[f738])).
% 9.33/1.58  fof(f741,plain,(
% 9.33/1.58    spl6_98 | ~spl6_6 | spl6_7 | ~spl6_10 | ~spl6_11 | spl6_12),
% 9.33/1.58    inference(avatar_split_clause,[],[f706,f128,f123,f118,f103,f98,f738])).
% 9.33/1.58  fof(f706,plain,(
% 9.33/1.58    sP0(sK4,sK4,sK2) | (~spl6_6 | spl6_7 | ~spl6_10 | ~spl6_11 | spl6_12)),
% 9.33/1.58    inference(unit_resulting_resolution,[],[f130,f125,f120,f105,f100,f105,f100,f66])).
% 9.33/1.58  fof(f66,plain,(
% 9.33/1.58    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 9.33/1.58    inference(cnf_transformation,[],[f27])).
% 9.33/1.58  fof(f27,plain,(
% 9.33/1.58    ! [X0,X1,X2] : (sP0(X2,X1,X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 9.33/1.58    inference(definition_folding,[],[f23,f26])).
% 9.33/1.58  fof(f23,plain,(
% 9.33/1.58    ! [X0,X1,X2] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 9.33/1.58    inference(flattening,[],[f22])).
% 9.33/1.58  fof(f22,plain,(
% 9.33/1.58    ! [X0,X1,X2] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 9.33/1.58    inference(ennf_transformation,[],[f5])).
% 9.33/1.58  fof(f5,axiom,(
% 9.33/1.58    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 9.33/1.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_tmap_1)).
% 9.33/1.58  fof(f647,plain,(
% 9.33/1.58    spl6_84 | ~spl6_10 | ~spl6_54),
% 9.33/1.58    inference(avatar_split_clause,[],[f624,f474,f118,f644])).
% 9.33/1.58  fof(f474,plain,(
% 9.33/1.58    spl6_54 <=> sP1(sK2,sK4,sK4)),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).
% 9.33/1.58  fof(f624,plain,(
% 9.33/1.58    l1_pre_topc(k1_tsep_1(sK2,sK4,sK4)) | (~spl6_10 | ~spl6_54)),
% 9.33/1.58    inference(unit_resulting_resolution,[],[f120,f476,f199])).
% 9.33/1.58  fof(f476,plain,(
% 9.33/1.58    sP1(sK2,sK4,sK4) | ~spl6_54),
% 9.33/1.58    inference(avatar_component_clause,[],[f474])).
% 9.33/1.58  fof(f594,plain,(
% 9.33/1.58    spl6_75 | ~spl6_51),
% 9.33/1.58    inference(avatar_split_clause,[],[f577,f459,f591])).
% 9.33/1.58  fof(f459,plain,(
% 9.33/1.58    spl6_51 <=> sP1(sK2,sK5,sK3)),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_51])])).
% 9.33/1.58  fof(f577,plain,(
% 9.33/1.58    m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK2) | ~spl6_51),
% 9.33/1.58    inference(unit_resulting_resolution,[],[f461,f69])).
% 9.33/1.58  fof(f461,plain,(
% 9.33/1.58    sP1(sK2,sK5,sK3) | ~spl6_51),
% 9.33/1.58    inference(avatar_component_clause,[],[f459])).
% 9.33/1.58  fof(f589,plain,(
% 9.33/1.58    spl6_74 | ~spl6_51),
% 9.33/1.58    inference(avatar_split_clause,[],[f578,f459,f586])).
% 9.33/1.58  fof(f578,plain,(
% 9.33/1.58    v1_pre_topc(k1_tsep_1(sK2,sK3,sK5)) | ~spl6_51),
% 9.33/1.58    inference(unit_resulting_resolution,[],[f461,f68])).
% 9.33/1.58  fof(f584,plain,(
% 9.33/1.58    ~spl6_73 | ~spl6_51),
% 9.33/1.58    inference(avatar_split_clause,[],[f579,f459,f581])).
% 9.33/1.58  fof(f579,plain,(
% 9.33/1.58    ~v2_struct_0(k1_tsep_1(sK2,sK3,sK5)) | ~spl6_51),
% 9.33/1.58    inference(unit_resulting_resolution,[],[f461,f67])).
% 9.33/1.58  fof(f477,plain,(
% 9.33/1.58    spl6_54 | ~spl6_6 | spl6_7 | ~spl6_10 | spl6_12),
% 9.33/1.58    inference(avatar_split_clause,[],[f376,f128,f118,f103,f98,f474])).
% 9.33/1.58  fof(f376,plain,(
% 9.33/1.58    sP1(sK2,sK4,sK4) | (~spl6_6 | spl6_7 | ~spl6_10 | spl6_12)),
% 9.33/1.58    inference(unit_resulting_resolution,[],[f130,f120,f105,f100,f105,f100,f70])).
% 9.33/1.58  fof(f70,plain,(
% 9.33/1.58    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 9.33/1.58    inference(cnf_transformation,[],[f29])).
% 9.33/1.58  fof(f29,plain,(
% 9.33/1.58    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 9.33/1.58    inference(definition_folding,[],[f25,f28])).
% 9.33/1.58  fof(f25,plain,(
% 9.33/1.58    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 9.33/1.58    inference(flattening,[],[f24])).
% 9.33/1.58  fof(f24,plain,(
% 9.33/1.58    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 9.33/1.58    inference(ennf_transformation,[],[f4])).
% 9.33/1.58  fof(f4,axiom,(
% 9.33/1.58    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 9.33/1.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 9.33/1.58  fof(f462,plain,(
% 9.33/1.58    spl6_51 | ~spl6_4 | spl6_5 | ~spl6_8 | spl6_9 | ~spl6_10 | spl6_12),
% 9.33/1.58    inference(avatar_split_clause,[],[f379,f128,f118,f113,f108,f93,f88,f459])).
% 9.33/1.58  fof(f379,plain,(
% 9.33/1.58    sP1(sK2,sK5,sK3) | (~spl6_4 | spl6_5 | ~spl6_8 | spl6_9 | ~spl6_10 | spl6_12)),
% 9.33/1.58    inference(unit_resulting_resolution,[],[f130,f120,f115,f110,f95,f90,f70])).
% 9.33/1.58  fof(f437,plain,(
% 9.33/1.58    spl6_46 | ~spl6_2 | ~spl6_3 | spl6_5 | spl6_7 | spl6_9 | ~spl6_15),
% 9.33/1.58    inference(avatar_split_clause,[],[f384,f156,f113,f103,f93,f83,f78,f434])).
% 9.33/1.58  fof(f384,plain,(
% 9.33/1.58    sP1(sK4,sK5,sK3) | (~spl6_2 | ~spl6_3 | spl6_5 | spl6_7 | spl6_9 | ~spl6_15)),
% 9.33/1.58    inference(unit_resulting_resolution,[],[f105,f158,f115,f85,f95,f80,f70])).
% 9.33/1.58  fof(f219,plain,(
% 9.33/1.58    spl6_21 | ~spl6_15 | ~spl6_18),
% 9.33/1.58    inference(avatar_split_clause,[],[f207,f183,f156,f216])).
% 9.33/1.58  fof(f183,plain,(
% 9.33/1.58    spl6_18 <=> m1_pre_topc(sK4,sK4)),
% 9.33/1.58    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 9.33/1.58  fof(f207,plain,(
% 9.33/1.58    m1_pre_topc(sK4,g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | (~spl6_15 | ~spl6_18)),
% 9.33/1.58    inference(unit_resulting_resolution,[],[f158,f158,f185,f55])).
% 9.33/1.58  fof(f185,plain,(
% 9.33/1.58    m1_pre_topc(sK4,sK4) | ~spl6_18),
% 9.33/1.58    inference(avatar_component_clause,[],[f183])).
% 9.33/1.58  fof(f186,plain,(
% 9.33/1.58    spl6_18 | ~spl6_15),
% 9.33/1.58    inference(avatar_split_clause,[],[f181,f156,f183])).
% 9.33/1.58  fof(f181,plain,(
% 9.33/1.58    m1_pre_topc(sK4,sK4) | ~spl6_15),
% 9.33/1.58    inference(unit_resulting_resolution,[],[f158,f54])).
% 9.33/1.58  fof(f54,plain,(
% 9.33/1.58    ( ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0)) )),
% 9.33/1.58    inference(cnf_transformation,[],[f13])).
% 9.33/1.58  fof(f13,plain,(
% 9.33/1.58    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 9.33/1.58    inference(ennf_transformation,[],[f7])).
% 9.33/1.58  fof(f7,axiom,(
% 9.33/1.58    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 9.33/1.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_tsep_1)).
% 9.33/1.58  fof(f170,plain,(
% 9.33/1.58    spl6_15 | ~spl6_6 | ~spl6_10),
% 9.33/1.58    inference(avatar_split_clause,[],[f169,f118,f98,f156])).
% 9.33/1.58  fof(f169,plain,(
% 9.33/1.58    l1_pre_topc(sK4) | (~spl6_6 | ~spl6_10)),
% 9.33/1.58    inference(subsumption_resolution,[],[f146,f120])).
% 9.33/1.58  fof(f146,plain,(
% 9.33/1.58    l1_pre_topc(sK4) | ~l1_pre_topc(sK2) | ~spl6_6),
% 9.33/1.58    inference(resolution,[],[f57,f100])).
% 9.33/1.58  fof(f131,plain,(
% 9.33/1.58    ~spl6_12),
% 9.33/1.58    inference(avatar_split_clause,[],[f42,f128])).
% 9.33/1.58  fof(f42,plain,(
% 9.33/1.58    ~v2_struct_0(sK2)),
% 9.33/1.58    inference(cnf_transformation,[],[f34])).
% 9.33/1.58  fof(f34,plain,(
% 9.33/1.58    (((~m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK4) & m1_pre_topc(sK5,sK4) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 9.33/1.58    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f12,f33,f32,f31,f30])).
% 9.33/1.58  fof(f30,plain,(
% 9.33/1.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK2,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 9.33/1.58    introduced(choice_axiom,[])).
% 9.33/1.58  fof(f31,plain,(
% 9.33/1.58    ? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK2,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK2,sK3,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK3,X2) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3))),
% 9.33/1.58    introduced(choice_axiom,[])).
% 9.33/1.58  fof(f32,plain,(
% 9.33/1.58    ? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK2,sK3,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK3,X2) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k1_tsep_1(sK2,sK3,X3),sK4) & m1_pre_topc(X3,sK4) & m1_pre_topc(sK3,sK4) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4))),
% 9.33/1.58    introduced(choice_axiom,[])).
% 9.33/1.58  fof(f33,plain,(
% 9.33/1.58    ? [X3] : (~m1_pre_topc(k1_tsep_1(sK2,sK3,X3),sK4) & m1_pre_topc(X3,sK4) & m1_pre_topc(sK3,sK4) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) => (~m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK4) & m1_pre_topc(sK5,sK4) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5))),
% 9.33/1.58    introduced(choice_axiom,[])).
% 9.33/1.58  fof(f12,plain,(
% 9.33/1.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 9.33/1.58    inference(flattening,[],[f11])).
% 9.33/1.58  fof(f11,plain,(
% 9.33/1.58    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & (m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 9.33/1.58    inference(ennf_transformation,[],[f10])).
% 9.33/1.58  fof(f10,negated_conjecture,(
% 9.33/1.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 9.33/1.58    inference(negated_conjecture,[],[f9])).
% 9.33/1.58  fof(f9,conjecture,(
% 9.33/1.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 9.33/1.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tmap_1)).
% 9.33/1.58  fof(f126,plain,(
% 9.33/1.58    spl6_11),
% 9.33/1.58    inference(avatar_split_clause,[],[f43,f123])).
% 9.33/1.58  fof(f43,plain,(
% 9.33/1.58    v2_pre_topc(sK2)),
% 9.33/1.58    inference(cnf_transformation,[],[f34])).
% 9.33/1.58  fof(f121,plain,(
% 9.33/1.58    spl6_10),
% 9.33/1.58    inference(avatar_split_clause,[],[f44,f118])).
% 9.33/1.58  fof(f44,plain,(
% 9.33/1.58    l1_pre_topc(sK2)),
% 9.33/1.58    inference(cnf_transformation,[],[f34])).
% 9.33/1.58  fof(f116,plain,(
% 9.33/1.58    ~spl6_9),
% 9.33/1.58    inference(avatar_split_clause,[],[f45,f113])).
% 9.33/1.58  fof(f45,plain,(
% 9.33/1.58    ~v2_struct_0(sK3)),
% 9.33/1.58    inference(cnf_transformation,[],[f34])).
% 9.33/1.58  fof(f111,plain,(
% 9.33/1.58    spl6_8),
% 9.33/1.58    inference(avatar_split_clause,[],[f46,f108])).
% 9.33/1.58  fof(f46,plain,(
% 9.33/1.58    m1_pre_topc(sK3,sK2)),
% 9.33/1.58    inference(cnf_transformation,[],[f34])).
% 9.33/1.58  fof(f106,plain,(
% 9.33/1.58    ~spl6_7),
% 9.33/1.58    inference(avatar_split_clause,[],[f47,f103])).
% 9.33/1.58  fof(f47,plain,(
% 9.33/1.58    ~v2_struct_0(sK4)),
% 9.33/1.58    inference(cnf_transformation,[],[f34])).
% 9.33/1.58  fof(f101,plain,(
% 9.33/1.58    spl6_6),
% 9.33/1.58    inference(avatar_split_clause,[],[f48,f98])).
% 9.33/1.58  fof(f48,plain,(
% 9.33/1.58    m1_pre_topc(sK4,sK2)),
% 9.33/1.58    inference(cnf_transformation,[],[f34])).
% 9.33/1.58  fof(f96,plain,(
% 9.33/1.58    ~spl6_5),
% 9.33/1.58    inference(avatar_split_clause,[],[f49,f93])).
% 9.33/1.58  fof(f49,plain,(
% 9.33/1.58    ~v2_struct_0(sK5)),
% 9.33/1.58    inference(cnf_transformation,[],[f34])).
% 9.33/1.58  fof(f91,plain,(
% 9.33/1.58    spl6_4),
% 9.33/1.58    inference(avatar_split_clause,[],[f50,f88])).
% 9.33/1.58  fof(f50,plain,(
% 9.33/1.58    m1_pre_topc(sK5,sK2)),
% 9.33/1.58    inference(cnf_transformation,[],[f34])).
% 9.33/1.58  fof(f86,plain,(
% 9.33/1.58    spl6_3),
% 9.33/1.58    inference(avatar_split_clause,[],[f51,f83])).
% 9.33/1.58  fof(f51,plain,(
% 9.33/1.58    m1_pre_topc(sK3,sK4)),
% 9.33/1.58    inference(cnf_transformation,[],[f34])).
% 9.33/1.58  fof(f81,plain,(
% 9.33/1.58    spl6_2),
% 9.33/1.58    inference(avatar_split_clause,[],[f52,f78])).
% 9.33/1.58  fof(f52,plain,(
% 9.33/1.58    m1_pre_topc(sK5,sK4)),
% 9.33/1.58    inference(cnf_transformation,[],[f34])).
% 9.33/1.58  fof(f76,plain,(
% 9.33/1.58    ~spl6_1),
% 9.33/1.58    inference(avatar_split_clause,[],[f53,f73])).
% 9.33/1.58  fof(f53,plain,(
% 9.33/1.58    ~m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK4)),
% 9.33/1.58    inference(cnf_transformation,[],[f34])).
% 9.33/1.58  % SZS output end Proof for theBenchmark
% 9.33/1.58  % (21270)------------------------------
% 9.33/1.58  % (21270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 9.33/1.58  % (21270)Termination reason: Refutation
% 9.33/1.58  
% 9.33/1.58  % (21270)Memory used [KB]: 31470
% 9.33/1.58  % (21270)Time elapsed: 1.146 s
% 9.33/1.58  % (21270)------------------------------
% 9.33/1.58  % (21270)------------------------------
% 9.33/1.59  % (21253)Success in time 1.225 s
%------------------------------------------------------------------------------
