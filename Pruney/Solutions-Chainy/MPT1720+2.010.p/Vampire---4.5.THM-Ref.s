%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:04 EST 2020

% Result     : Theorem 6.53s
% Output     : Refutation 6.53s
% Verified   : 
% Statistics : Number of formulae       :  192 ( 550 expanded)
%              Number of leaves         :   47 ( 268 expanded)
%              Depth                    :   10
%              Number of atoms          :  822 (2918 expanded)
%              Number of equality atoms :   23 (  40 expanded)
%              Maximal formula depth    :   21 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f14641,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f97,f102,f107,f112,f117,f122,f127,f132,f161,f268,f278,f303,f428,f461,f466,f471,f510,f618,f648,f766,f771,f776,f781,f818,f3152,f3263,f3281,f4586,f14638])).

fof(f14638,plain,
    ( ~ spl6_2
    | ~ spl6_3
    | spl6_5
    | spl6_7
    | spl6_9
    | ~ spl6_14
    | ~ spl6_55
    | ~ spl6_85
    | spl6_103
    | ~ spl6_104
    | ~ spl6_105
    | ~ spl6_111
    | spl6_494
    | ~ spl6_700 ),
    inference(avatar_contradiction_clause,[],[f14637])).

fof(f14637,plain,
    ( $false
    | ~ spl6_2
    | ~ spl6_3
    | spl6_5
    | spl6_7
    | spl6_9
    | ~ spl6_14
    | ~ spl6_55
    | ~ spl6_85
    | spl6_103
    | ~ spl6_104
    | ~ spl6_105
    | ~ spl6_111
    | spl6_494
    | ~ spl6_700 ),
    inference(subsumption_resolution,[],[f14622,f4585])).

fof(f4585,plain,
    ( m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),k1_tsep_1(sK2,sK4,sK4))
    | ~ spl6_700 ),
    inference(avatar_component_clause,[],[f4583])).

fof(f4583,plain,
    ( spl6_700
  <=> m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),k1_tsep_1(sK2,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_700])])).

fof(f14622,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),k1_tsep_1(sK2,sK4,sK4))
    | ~ spl6_2
    | ~ spl6_3
    | spl6_5
    | spl6_7
    | spl6_9
    | ~ spl6_14
    | ~ spl6_55
    | ~ spl6_85
    | spl6_103
    | ~ spl6_104
    | ~ spl6_105
    | ~ spl6_111
    | spl6_494 ),
    inference(unit_resulting_resolution,[],[f106,f149,f116,f96,f427,f617,f817,f86,f81,f765,f770,f775,f775,f3280,f874])).

fof(f874,plain,(
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
    inference(superposition,[],[f63,f72])).

fof(f72,plain,(
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
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
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
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).

fof(f3280,plain,
    ( ~ r1_tarski(k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5)),u1_struct_0(sK4))
    | spl6_494 ),
    inference(avatar_component_clause,[],[f3278])).

fof(f3278,plain,
    ( spl6_494
  <=> r1_tarski(k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5)),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_494])])).

fof(f775,plain,
    ( m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),sK4)
    | ~ spl6_105 ),
    inference(avatar_component_clause,[],[f773])).

fof(f773,plain,
    ( spl6_105
  <=> m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_105])])).

fof(f770,plain,
    ( v1_pre_topc(k1_tsep_1(sK4,sK3,sK5))
    | ~ spl6_104 ),
    inference(avatar_component_clause,[],[f768])).

fof(f768,plain,
    ( spl6_104
  <=> v1_pre_topc(k1_tsep_1(sK4,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_104])])).

fof(f765,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK4,sK3,sK5))
    | spl6_103 ),
    inference(avatar_component_clause,[],[f763])).

fof(f763,plain,
    ( spl6_103
  <=> v2_struct_0(k1_tsep_1(sK4,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_103])])).

fof(f81,plain,
    ( m1_pre_topc(sK5,sK4)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f79])).

fof(f79,plain,
    ( spl6_2
  <=> m1_pre_topc(sK5,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f86,plain,
    ( m1_pre_topc(sK3,sK4)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f84])).

fof(f84,plain,
    ( spl6_3
  <=> m1_pre_topc(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f817,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK2,sK4,sK4))
    | ~ spl6_111 ),
    inference(avatar_component_clause,[],[f815])).

fof(f815,plain,
    ( spl6_111
  <=> m1_pre_topc(sK4,k1_tsep_1(sK2,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_111])])).

fof(f617,plain,
    ( v2_pre_topc(k1_tsep_1(sK2,sK4,sK4))
    | ~ spl6_85 ),
    inference(avatar_component_clause,[],[f615])).

fof(f615,plain,
    ( spl6_85
  <=> v2_pre_topc(k1_tsep_1(sK2,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).

fof(f427,plain,
    ( l1_pre_topc(k1_tsep_1(sK2,sK4,sK4))
    | ~ spl6_55 ),
    inference(avatar_component_clause,[],[f425])).

fof(f425,plain,
    ( spl6_55
  <=> l1_pre_topc(k1_tsep_1(sK2,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f96,plain,
    ( ~ v2_struct_0(sK5)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f94])).

fof(f94,plain,
    ( spl6_5
  <=> v2_struct_0(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f116,plain,
    ( ~ v2_struct_0(sK3)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl6_9
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f149,plain,
    ( l1_pre_topc(sK4)
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f147])).

fof(f147,plain,
    ( spl6_14
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f106,plain,
    ( ~ v2_struct_0(sK4)
    | spl6_7 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl6_7
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f4586,plain,
    ( spl6_700
    | ~ spl6_14
    | ~ spl6_87
    | ~ spl6_105
    | ~ spl6_106 ),
    inference(avatar_split_clause,[],[f4581,f778,f773,f645,f147,f4583])).

fof(f645,plain,
    ( spl6_87
  <=> g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k1_tsep_1(sK2,sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).

fof(f778,plain,
    ( spl6_106
  <=> l1_pre_topc(k1_tsep_1(sK4,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_106])])).

fof(f4581,plain,
    ( m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),k1_tsep_1(sK2,sK4,sK4))
    | ~ spl6_14
    | ~ spl6_87
    | ~ spl6_105
    | ~ spl6_106 ),
    inference(forward_demodulation,[],[f4522,f647])).

fof(f647,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k1_tsep_1(sK2,sK4,sK4)
    | ~ spl6_87 ),
    inference(avatar_component_clause,[],[f645])).

fof(f4522,plain,
    ( m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)))
    | ~ spl6_14
    | ~ spl6_105
    | ~ spl6_106 ),
    inference(unit_resulting_resolution,[],[f149,f780,f775,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( m1_pre_topc(X0,X1)
              | ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
            & ( m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
              | ~ m1_pre_topc(X0,X1) ) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f780,plain,
    ( l1_pre_topc(k1_tsep_1(sK4,sK3,sK5))
    | ~ spl6_106 ),
    inference(avatar_component_clause,[],[f778])).

fof(f3281,plain,
    ( ~ spl6_494
    | spl6_469
    | ~ spl6_491 ),
    inference(avatar_split_clause,[],[f3276,f3260,f3149,f3278])).

fof(f3149,plain,
    ( spl6_469
  <=> r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK3,sK5)),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_469])])).

fof(f3260,plain,
    ( spl6_491
  <=> u1_struct_0(k1_tsep_1(sK2,sK3,sK5)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_491])])).

fof(f3276,plain,
    ( ~ r1_tarski(k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5)),u1_struct_0(sK4))
    | spl6_469
    | ~ spl6_491 ),
    inference(forward_demodulation,[],[f3151,f3262])).

fof(f3262,plain,
    ( u1_struct_0(k1_tsep_1(sK2,sK3,sK5)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5))
    | ~ spl6_491 ),
    inference(avatar_component_clause,[],[f3260])).

fof(f3151,plain,
    ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK3,sK5)),u1_struct_0(sK4))
    | spl6_469 ),
    inference(avatar_component_clause,[],[f3149])).

fof(f3263,plain,
    ( spl6_491
    | ~ spl6_4
    | spl6_5
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_12
    | spl6_60
    | ~ spl6_61
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f2884,f468,f463,f458,f129,f119,f114,f109,f94,f89,f3260])).

fof(f89,plain,
    ( spl6_4
  <=> m1_pre_topc(sK5,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f109,plain,
    ( spl6_8
  <=> m1_pre_topc(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f119,plain,
    ( spl6_10
  <=> l1_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f129,plain,
    ( spl6_12
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f458,plain,
    ( spl6_60
  <=> v2_struct_0(k1_tsep_1(sK2,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).

fof(f463,plain,
    ( spl6_61
  <=> v1_pre_topc(k1_tsep_1(sK2,sK3,sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).

fof(f468,plain,
    ( spl6_62
  <=> m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f2884,plain,
    ( u1_struct_0(k1_tsep_1(sK2,sK3,sK5)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5))
    | ~ spl6_4
    | spl6_5
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_12
    | spl6_60
    | ~ spl6_61
    | ~ spl6_62 ),
    inference(unit_resulting_resolution,[],[f131,f121,f116,f96,f111,f91,f460,f465,f470,f72])).

fof(f470,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK2)
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f468])).

fof(f465,plain,
    ( v1_pre_topc(k1_tsep_1(sK2,sK3,sK5))
    | ~ spl6_61 ),
    inference(avatar_component_clause,[],[f463])).

fof(f460,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK2,sK3,sK5))
    | spl6_60 ),
    inference(avatar_component_clause,[],[f458])).

fof(f91,plain,
    ( m1_pre_topc(sK5,sK2)
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f111,plain,
    ( m1_pre_topc(sK3,sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f109])).

fof(f121,plain,
    ( l1_pre_topc(sK2)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f131,plain,
    ( ~ v2_struct_0(sK2)
    | spl6_12 ),
    inference(avatar_component_clause,[],[f129])).

fof(f3152,plain,
    ( ~ spl6_469
    | spl6_1
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_62 ),
    inference(avatar_split_clause,[],[f2908,f468,f124,f119,f99,f74,f3149])).

fof(f74,plain,
    ( spl6_1
  <=> m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f99,plain,
    ( spl6_6
  <=> m1_pre_topc(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f124,plain,
    ( spl6_11
  <=> v2_pre_topc(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f2908,plain,
    ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK3,sK5)),u1_struct_0(sK4))
    | spl6_1
    | ~ spl6_6
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_62 ),
    inference(unit_resulting_resolution,[],[f126,f121,f101,f76,f470,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f76,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK4)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f74])).

fof(f101,plain,
    ( m1_pre_topc(sK4,sK2)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f99])).

fof(f126,plain,
    ( v2_pre_topc(sK2)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f124])).

fof(f818,plain,
    ( spl6_111
    | ~ spl6_6
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | spl6_12 ),
    inference(avatar_split_clause,[],[f786,f129,f124,f119,f104,f99,f815])).

fof(f786,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK2,sK4,sK4))
    | ~ spl6_6
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | spl6_12 ),
    inference(unit_resulting_resolution,[],[f131,f126,f121,f106,f101,f106,f101,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_pre_topc(X1,k1_tsep_1(X0,X1,X2))
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
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
         => ! [X2] :
              ( ( m1_pre_topc(X2,X0)
                & ~ v2_struct_0(X2) )
             => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tsep_1)).

fof(f781,plain,
    ( spl6_106
    | ~ spl6_14
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f758,f300,f147,f778])).

fof(f300,plain,
    ( spl6_34
  <=> sP1(sK4,sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f758,plain,
    ( l1_pre_topc(k1_tsep_1(sK4,sK3,sK5))
    | ~ spl6_14
    | ~ spl6_34 ),
    inference(unit_resulting_resolution,[],[f149,f302,f166])).

fof(f166,plain,(
    ! [X2,X0,X1] :
      ( l1_pre_topc(k1_tsep_1(X0,X2,X1))
      | ~ sP1(X0,X1,X2)
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f70,f57])).

fof(f57,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
        & v1_pre_topc(k1_tsep_1(X0,X2,X1))
        & ~ v2_struct_0(k1_tsep_1(X0,X2,X1)) )
      | ~ sP1(X0,X1,X2) ) ),
    inference(rectify,[],[f41])).

fof(f41,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP1(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP1(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).

fof(f302,plain,
    ( sP1(sK4,sK5,sK3)
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f300])).

fof(f776,plain,
    ( spl6_105
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f759,f300,f773])).

fof(f759,plain,
    ( m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),sK4)
    | ~ spl6_34 ),
    inference(unit_resulting_resolution,[],[f302,f70])).

fof(f771,plain,
    ( spl6_104
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f760,f300,f768])).

fof(f760,plain,
    ( v1_pre_topc(k1_tsep_1(sK4,sK3,sK5))
    | ~ spl6_34 ),
    inference(unit_resulting_resolution,[],[f302,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X2,X1))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f766,plain,
    ( ~ spl6_103
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f761,f300,f763])).

fof(f761,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK4,sK3,sK5))
    | ~ spl6_34 ),
    inference(unit_resulting_resolution,[],[f302,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X2,X1))
      | ~ sP1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f648,plain,
    ( spl6_87
    | ~ spl6_6
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | spl6_12 ),
    inference(avatar_split_clause,[],[f620,f129,f124,f119,f104,f99,f645])).

fof(f620,plain,
    ( g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k1_tsep_1(sK2,sK4,sK4)
    | ~ spl6_6
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | spl6_12 ),
    inference(unit_resulting_resolution,[],[f131,f126,f121,f106,f101,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tmap_1)).

fof(f618,plain,
    ( spl6_85
    | ~ spl6_68 ),
    inference(avatar_split_clause,[],[f611,f507,f615])).

fof(f507,plain,
    ( spl6_68
  <=> sP0(sK4,sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).

fof(f611,plain,
    ( v2_pre_topc(k1_tsep_1(sK2,sK4,sK4))
    | ~ spl6_68 ),
    inference(unit_resulting_resolution,[],[f509,f66])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( v2_pre_topc(k1_tsep_1(X2,X1,X0))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( v2_pre_topc(k1_tsep_1(X2,X1,X0))
        & v1_pre_topc(k1_tsep_1(X2,X1,X0))
        & ~ v2_struct_0(k1_tsep_1(X2,X1,X0)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f39])).

fof(f39,plain,(
    ! [X2,X1,X0] :
      ( ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP0(X2,X1,X0) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X2,X1,X0] :
      ( ( v2_pre_topc(k1_tsep_1(X0,X1,X2))
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP0(X2,X1,X0) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f509,plain,
    ( sP0(sK4,sK4,sK2)
    | ~ spl6_68 ),
    inference(avatar_component_clause,[],[f507])).

fof(f510,plain,
    ( spl6_68
    | ~ spl6_6
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | spl6_12 ),
    inference(avatar_split_clause,[],[f481,f129,f124,f119,f104,f99,f507])).

fof(f481,plain,
    ( sP0(sK4,sK4,sK2)
    | ~ spl6_6
    | spl6_7
    | ~ spl6_10
    | ~ spl6_11
    | spl6_12 ),
    inference(unit_resulting_resolution,[],[f131,f126,f121,f106,f101,f106,f101,f67])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( sP0(X2,X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( sP0(X2,X1,X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f24,f27])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tmap_1)).

fof(f471,plain,
    ( spl6_62
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f454,f275,f468])).

fof(f275,plain,
    ( spl6_29
  <=> sP1(sK2,sK5,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f454,plain,
    ( m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK2)
    | ~ spl6_29 ),
    inference(unit_resulting_resolution,[],[f277,f70])).

fof(f277,plain,
    ( sP1(sK2,sK5,sK3)
    | ~ spl6_29 ),
    inference(avatar_component_clause,[],[f275])).

fof(f466,plain,
    ( spl6_61
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f455,f275,f463])).

fof(f455,plain,
    ( v1_pre_topc(k1_tsep_1(sK2,sK3,sK5))
    | ~ spl6_29 ),
    inference(unit_resulting_resolution,[],[f277,f69])).

fof(f461,plain,
    ( ~ spl6_60
    | ~ spl6_29 ),
    inference(avatar_split_clause,[],[f456,f275,f458])).

fof(f456,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK2,sK3,sK5))
    | ~ spl6_29 ),
    inference(unit_resulting_resolution,[],[f277,f68])).

fof(f428,plain,
    ( spl6_55
    | ~ spl6_10
    | ~ spl6_27 ),
    inference(avatar_split_clause,[],[f405,f265,f119,f425])).

fof(f265,plain,
    ( spl6_27
  <=> sP1(sK2,sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f405,plain,
    ( l1_pre_topc(k1_tsep_1(sK2,sK4,sK4))
    | ~ spl6_10
    | ~ spl6_27 ),
    inference(unit_resulting_resolution,[],[f121,f267,f166])).

fof(f267,plain,
    ( sP1(sK2,sK4,sK4)
    | ~ spl6_27 ),
    inference(avatar_component_clause,[],[f265])).

fof(f303,plain,
    ( spl6_34
    | ~ spl6_2
    | ~ spl6_3
    | spl6_5
    | spl6_7
    | spl6_9
    | ~ spl6_14 ),
    inference(avatar_split_clause,[],[f232,f147,f114,f104,f94,f84,f79,f300])).

fof(f232,plain,
    ( sP1(sK4,sK5,sK3)
    | ~ spl6_2
    | ~ spl6_3
    | spl6_5
    | spl6_7
    | spl6_9
    | ~ spl6_14 ),
    inference(unit_resulting_resolution,[],[f106,f149,f116,f86,f96,f81,f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( sP1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( sP1(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f26,f29])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).

fof(f278,plain,
    ( spl6_29
    | ~ spl6_4
    | spl6_5
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_12 ),
    inference(avatar_split_clause,[],[f237,f129,f119,f114,f109,f94,f89,f275])).

fof(f237,plain,
    ( sP1(sK2,sK5,sK3)
    | ~ spl6_4
    | spl6_5
    | ~ spl6_8
    | spl6_9
    | ~ spl6_10
    | spl6_12 ),
    inference(unit_resulting_resolution,[],[f131,f121,f116,f111,f96,f91,f71])).

fof(f268,plain,
    ( spl6_27
    | ~ spl6_6
    | spl6_7
    | ~ spl6_10
    | spl6_12 ),
    inference(avatar_split_clause,[],[f239,f129,f119,f104,f99,f265])).

fof(f239,plain,
    ( sP1(sK2,sK4,sK4)
    | ~ spl6_6
    | spl6_7
    | ~ spl6_10
    | spl6_12 ),
    inference(unit_resulting_resolution,[],[f131,f121,f106,f101,f106,f101,f71])).

fof(f161,plain,
    ( spl6_14
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f160,f119,f99,f147])).

fof(f160,plain,
    ( l1_pre_topc(sK4)
    | ~ spl6_6
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f139,f121])).

fof(f139,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK2)
    | ~ spl6_6 ),
    inference(resolution,[],[f57,f101])).

fof(f132,plain,(
    ~ spl6_12 ),
    inference(avatar_split_clause,[],[f43,f129])).

fof(f43,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f12,f34,f33,f32,f31])).

fof(f31,plain,
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

fof(f32,plain,
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

fof(f33,plain,
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

fof(f34,plain,
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tmap_1)).

fof(f127,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f44,f124])).

fof(f44,plain,(
    v2_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f122,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f45,f119])).

fof(f45,plain,(
    l1_pre_topc(sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f117,plain,(
    ~ spl6_9 ),
    inference(avatar_split_clause,[],[f46,f114])).

fof(f46,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f35])).

fof(f112,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f47,f109])).

fof(f47,plain,(
    m1_pre_topc(sK3,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f107,plain,(
    ~ spl6_7 ),
    inference(avatar_split_clause,[],[f48,f104])).

fof(f48,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f102,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f49,f99])).

fof(f49,plain,(
    m1_pre_topc(sK4,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f97,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f50,f94])).

fof(f50,plain,(
    ~ v2_struct_0(sK5) ),
    inference(cnf_transformation,[],[f35])).

fof(f92,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f51,f89])).

fof(f51,plain,(
    m1_pre_topc(sK5,sK2) ),
    inference(cnf_transformation,[],[f35])).

fof(f87,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f52,f84])).

fof(f52,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f82,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f53,f79])).

fof(f53,plain,(
    m1_pre_topc(sK5,sK4) ),
    inference(cnf_transformation,[],[f35])).

fof(f77,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f54,f74])).

fof(f54,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK4) ),
    inference(cnf_transformation,[],[f35])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n023.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:24:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.42  % (13229)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.45  % (13238)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.46  % (13239)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.47  % (13234)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (13240)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.48  % (13228)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (13232)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.49  % (13224)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (13230)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (13245)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.50  % (13245)Refutation not found, incomplete strategy% (13245)------------------------------
% 0.21/0.50  % (13245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (13245)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (13245)Memory used [KB]: 10618
% 0.21/0.50  % (13245)Time elapsed: 0.095 s
% 0.21/0.50  % (13245)------------------------------
% 0.21/0.50  % (13245)------------------------------
% 0.21/0.51  % (13237)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (13244)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.51  % (13227)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (13235)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.51  % (13226)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (13225)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  % (13225)Refutation not found, incomplete strategy% (13225)------------------------------
% 0.21/0.51  % (13225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (13225)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (13225)Memory used [KB]: 10618
% 0.21/0.51  % (13225)Time elapsed: 0.098 s
% 0.21/0.51  % (13225)------------------------------
% 0.21/0.51  % (13225)------------------------------
% 0.21/0.52  % (13241)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.52  % (13242)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.52  % (13236)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.52  % (13243)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.52  % (13231)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.52  % (13235)Refutation not found, incomplete strategy% (13235)------------------------------
% 0.21/0.52  % (13235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (13235)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (13235)Memory used [KB]: 6268
% 0.21/0.52  % (13235)Time elapsed: 0.106 s
% 0.21/0.52  % (13235)------------------------------
% 0.21/0.52  % (13235)------------------------------
% 3.99/0.90  % (13229)Time limit reached!
% 3.99/0.90  % (13229)------------------------------
% 3.99/0.90  % (13229)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.99/0.90  % (13229)Termination reason: Time limit
% 3.99/0.90  
% 3.99/0.90  % (13229)Memory used [KB]: 8571
% 3.99/0.90  % (13229)Time elapsed: 0.508 s
% 3.99/0.90  % (13229)------------------------------
% 3.99/0.90  % (13229)------------------------------
% 3.99/0.91  % (13224)Time limit reached!
% 3.99/0.91  % (13224)------------------------------
% 3.99/0.91  % (13224)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.99/0.91  % (13224)Termination reason: Time limit
% 3.99/0.91  % (13224)Termination phase: Saturation
% 3.99/0.91  
% 3.99/0.91  % (13224)Memory used [KB]: 14200
% 3.99/0.91  % (13224)Time elapsed: 0.500 s
% 3.99/0.91  % (13224)------------------------------
% 3.99/0.91  % (13224)------------------------------
% 3.99/0.91  % (13237)Time limit reached!
% 3.99/0.91  % (13237)------------------------------
% 3.99/0.91  % (13237)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 3.99/0.91  % (13237)Termination reason: Time limit
% 3.99/0.91  % (13237)Termination phase: Saturation
% 3.99/0.91  
% 3.99/0.91  % (13237)Memory used [KB]: 12409
% 3.99/0.91  % (13237)Time elapsed: 0.500 s
% 3.99/0.91  % (13237)------------------------------
% 3.99/0.91  % (13237)------------------------------
% 5.02/1.02  % (13232)Time limit reached!
% 5.02/1.02  % (13232)------------------------------
% 5.02/1.02  % (13232)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 5.02/1.02  % (13232)Termination reason: Time limit
% 5.02/1.02  % (13232)Termination phase: Saturation
% 5.02/1.02  
% 5.02/1.02  % (13232)Memory used [KB]: 8315
% 5.02/1.02  % (13232)Time elapsed: 0.600 s
% 5.02/1.02  % (13232)------------------------------
% 5.02/1.02  % (13232)------------------------------
% 6.53/1.18  % (13241)Refutation found. Thanks to Tanya!
% 6.53/1.18  % SZS status Theorem for theBenchmark
% 6.53/1.19  % SZS output start Proof for theBenchmark
% 6.53/1.19  fof(f14641,plain,(
% 6.53/1.19    $false),
% 6.53/1.19    inference(avatar_sat_refutation,[],[f77,f82,f87,f92,f97,f102,f107,f112,f117,f122,f127,f132,f161,f268,f278,f303,f428,f461,f466,f471,f510,f618,f648,f766,f771,f776,f781,f818,f3152,f3263,f3281,f4586,f14638])).
% 6.53/1.19  fof(f14638,plain,(
% 6.53/1.19    ~spl6_2 | ~spl6_3 | spl6_5 | spl6_7 | spl6_9 | ~spl6_14 | ~spl6_55 | ~spl6_85 | spl6_103 | ~spl6_104 | ~spl6_105 | ~spl6_111 | spl6_494 | ~spl6_700),
% 6.53/1.19    inference(avatar_contradiction_clause,[],[f14637])).
% 6.53/1.19  fof(f14637,plain,(
% 6.53/1.19    $false | (~spl6_2 | ~spl6_3 | spl6_5 | spl6_7 | spl6_9 | ~spl6_14 | ~spl6_55 | ~spl6_85 | spl6_103 | ~spl6_104 | ~spl6_105 | ~spl6_111 | spl6_494 | ~spl6_700)),
% 6.53/1.19    inference(subsumption_resolution,[],[f14622,f4585])).
% 6.53/1.19  fof(f4585,plain,(
% 6.53/1.19    m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),k1_tsep_1(sK2,sK4,sK4)) | ~spl6_700),
% 6.53/1.19    inference(avatar_component_clause,[],[f4583])).
% 6.53/1.19  fof(f4583,plain,(
% 6.53/1.19    spl6_700 <=> m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),k1_tsep_1(sK2,sK4,sK4))),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_700])])).
% 6.53/1.19  fof(f14622,plain,(
% 6.53/1.19    ~m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),k1_tsep_1(sK2,sK4,sK4)) | (~spl6_2 | ~spl6_3 | spl6_5 | spl6_7 | spl6_9 | ~spl6_14 | ~spl6_55 | ~spl6_85 | spl6_103 | ~spl6_104 | ~spl6_105 | ~spl6_111 | spl6_494)),
% 6.53/1.19    inference(unit_resulting_resolution,[],[f106,f149,f116,f96,f427,f617,f817,f86,f81,f765,f770,f775,f775,f3280,f874])).
% 6.53/1.19  fof(f874,plain,(
% 6.53/1.19    ( ! [X43,X41,X44,X42,X40] : (r1_tarski(k2_xboole_0(u1_struct_0(X41),u1_struct_0(X42)),u1_struct_0(X43)) | ~m1_pre_topc(k1_tsep_1(X40,X41,X42),X43) | ~m1_pre_topc(X43,X44) | ~m1_pre_topc(k1_tsep_1(X40,X41,X42),X44) | ~l1_pre_topc(X44) | ~v2_pre_topc(X44) | ~m1_pre_topc(k1_tsep_1(X40,X41,X42),X40) | ~v1_pre_topc(k1_tsep_1(X40,X41,X42)) | v2_struct_0(k1_tsep_1(X40,X41,X42)) | ~m1_pre_topc(X42,X40) | v2_struct_0(X42) | ~m1_pre_topc(X41,X40) | v2_struct_0(X41) | ~l1_pre_topc(X40) | v2_struct_0(X40)) )),
% 6.53/1.19    inference(superposition,[],[f63,f72])).
% 6.53/1.19  fof(f72,plain,(
% 6.53/1.19    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.53/1.19    inference(equality_resolution,[],[f60])).
% 6.53/1.19  fof(f60,plain,(
% 6.53/1.19    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.53/1.19    inference(cnf_transformation,[],[f37])).
% 6.53/1.19  fof(f37,plain,(
% 6.53/1.19    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 6.53/1.19    inference(nnf_transformation,[],[f20])).
% 6.53/1.19  fof(f20,plain,(
% 6.53/1.19    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 6.53/1.19    inference(flattening,[],[f19])).
% 6.53/1.19  fof(f19,plain,(
% 6.53/1.19    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 6.53/1.19    inference(ennf_transformation,[],[f3])).
% 6.53/1.19  fof(f3,axiom,(
% 6.53/1.19    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 6.53/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).
% 6.53/1.19  fof(f63,plain,(
% 6.53/1.19    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.53/1.19    inference(cnf_transformation,[],[f38])).
% 6.53/1.19  fof(f38,plain,(
% 6.53/1.19    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 6.53/1.19    inference(nnf_transformation,[],[f22])).
% 6.53/1.19  fof(f22,plain,(
% 6.53/1.19    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 6.53/1.19    inference(flattening,[],[f21])).
% 6.53/1.19  fof(f21,plain,(
% 6.53/1.19    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 6.53/1.19    inference(ennf_transformation,[],[f8])).
% 6.53/1.19  fof(f8,axiom,(
% 6.53/1.19    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 6.53/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_tsep_1)).
% 6.53/1.19  fof(f3280,plain,(
% 6.53/1.19    ~r1_tarski(k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5)),u1_struct_0(sK4)) | spl6_494),
% 6.53/1.19    inference(avatar_component_clause,[],[f3278])).
% 6.53/1.19  fof(f3278,plain,(
% 6.53/1.19    spl6_494 <=> r1_tarski(k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5)),u1_struct_0(sK4))),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_494])])).
% 6.53/1.19  fof(f775,plain,(
% 6.53/1.19    m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),sK4) | ~spl6_105),
% 6.53/1.19    inference(avatar_component_clause,[],[f773])).
% 6.53/1.19  fof(f773,plain,(
% 6.53/1.19    spl6_105 <=> m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),sK4)),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_105])])).
% 6.53/1.19  fof(f770,plain,(
% 6.53/1.19    v1_pre_topc(k1_tsep_1(sK4,sK3,sK5)) | ~spl6_104),
% 6.53/1.19    inference(avatar_component_clause,[],[f768])).
% 6.53/1.19  fof(f768,plain,(
% 6.53/1.19    spl6_104 <=> v1_pre_topc(k1_tsep_1(sK4,sK3,sK5))),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_104])])).
% 6.53/1.19  fof(f765,plain,(
% 6.53/1.19    ~v2_struct_0(k1_tsep_1(sK4,sK3,sK5)) | spl6_103),
% 6.53/1.19    inference(avatar_component_clause,[],[f763])).
% 6.53/1.19  fof(f763,plain,(
% 6.53/1.19    spl6_103 <=> v2_struct_0(k1_tsep_1(sK4,sK3,sK5))),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_103])])).
% 6.53/1.19  fof(f81,plain,(
% 6.53/1.19    m1_pre_topc(sK5,sK4) | ~spl6_2),
% 6.53/1.19    inference(avatar_component_clause,[],[f79])).
% 6.53/1.19  fof(f79,plain,(
% 6.53/1.19    spl6_2 <=> m1_pre_topc(sK5,sK4)),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 6.53/1.19  fof(f86,plain,(
% 6.53/1.19    m1_pre_topc(sK3,sK4) | ~spl6_3),
% 6.53/1.19    inference(avatar_component_clause,[],[f84])).
% 6.53/1.19  fof(f84,plain,(
% 6.53/1.19    spl6_3 <=> m1_pre_topc(sK3,sK4)),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 6.53/1.19  fof(f817,plain,(
% 6.53/1.19    m1_pre_topc(sK4,k1_tsep_1(sK2,sK4,sK4)) | ~spl6_111),
% 6.53/1.19    inference(avatar_component_clause,[],[f815])).
% 6.53/1.19  fof(f815,plain,(
% 6.53/1.19    spl6_111 <=> m1_pre_topc(sK4,k1_tsep_1(sK2,sK4,sK4))),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_111])])).
% 6.53/1.19  fof(f617,plain,(
% 6.53/1.19    v2_pre_topc(k1_tsep_1(sK2,sK4,sK4)) | ~spl6_85),
% 6.53/1.19    inference(avatar_component_clause,[],[f615])).
% 6.53/1.19  fof(f615,plain,(
% 6.53/1.19    spl6_85 <=> v2_pre_topc(k1_tsep_1(sK2,sK4,sK4))),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_85])])).
% 6.53/1.19  fof(f427,plain,(
% 6.53/1.19    l1_pre_topc(k1_tsep_1(sK2,sK4,sK4)) | ~spl6_55),
% 6.53/1.19    inference(avatar_component_clause,[],[f425])).
% 6.53/1.19  fof(f425,plain,(
% 6.53/1.19    spl6_55 <=> l1_pre_topc(k1_tsep_1(sK2,sK4,sK4))),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).
% 6.53/1.19  fof(f96,plain,(
% 6.53/1.19    ~v2_struct_0(sK5) | spl6_5),
% 6.53/1.19    inference(avatar_component_clause,[],[f94])).
% 6.53/1.19  fof(f94,plain,(
% 6.53/1.19    spl6_5 <=> v2_struct_0(sK5)),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 6.53/1.19  fof(f116,plain,(
% 6.53/1.19    ~v2_struct_0(sK3) | spl6_9),
% 6.53/1.19    inference(avatar_component_clause,[],[f114])).
% 6.53/1.19  fof(f114,plain,(
% 6.53/1.19    spl6_9 <=> v2_struct_0(sK3)),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 6.53/1.19  fof(f149,plain,(
% 6.53/1.19    l1_pre_topc(sK4) | ~spl6_14),
% 6.53/1.19    inference(avatar_component_clause,[],[f147])).
% 6.53/1.19  fof(f147,plain,(
% 6.53/1.19    spl6_14 <=> l1_pre_topc(sK4)),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 6.53/1.19  fof(f106,plain,(
% 6.53/1.19    ~v2_struct_0(sK4) | spl6_7),
% 6.53/1.19    inference(avatar_component_clause,[],[f104])).
% 6.53/1.19  fof(f104,plain,(
% 6.53/1.19    spl6_7 <=> v2_struct_0(sK4)),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 6.53/1.19  fof(f4586,plain,(
% 6.53/1.19    spl6_700 | ~spl6_14 | ~spl6_87 | ~spl6_105 | ~spl6_106),
% 6.53/1.19    inference(avatar_split_clause,[],[f4581,f778,f773,f645,f147,f4583])).
% 6.53/1.19  fof(f645,plain,(
% 6.53/1.19    spl6_87 <=> g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k1_tsep_1(sK2,sK4,sK4)),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_87])])).
% 6.53/1.19  fof(f778,plain,(
% 6.53/1.19    spl6_106 <=> l1_pre_topc(k1_tsep_1(sK4,sK3,sK5))),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_106])])).
% 6.53/1.19  fof(f4581,plain,(
% 6.53/1.19    m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),k1_tsep_1(sK2,sK4,sK4)) | (~spl6_14 | ~spl6_87 | ~spl6_105 | ~spl6_106)),
% 6.53/1.19    inference(forward_demodulation,[],[f4522,f647])).
% 6.53/1.19  fof(f647,plain,(
% 6.53/1.19    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k1_tsep_1(sK2,sK4,sK4) | ~spl6_87),
% 6.53/1.19    inference(avatar_component_clause,[],[f645])).
% 6.53/1.19  fof(f4522,plain,(
% 6.53/1.19    m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4))) | (~spl6_14 | ~spl6_105 | ~spl6_106)),
% 6.53/1.19    inference(unit_resulting_resolution,[],[f149,f780,f775,f55])).
% 6.53/1.19  fof(f55,plain,(
% 6.53/1.19    ( ! [X0,X1] : (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 6.53/1.19    inference(cnf_transformation,[],[f36])).
% 6.53/1.19  fof(f36,plain,(
% 6.53/1.19    ! [X0] : (! [X1] : (((m1_pre_topc(X0,X1) | ~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & (m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~m1_pre_topc(X0,X1))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 6.53/1.19    inference(nnf_transformation,[],[f13])).
% 6.53/1.19  fof(f13,plain,(
% 6.53/1.19    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 6.53/1.19    inference(ennf_transformation,[],[f2])).
% 6.53/1.19  fof(f2,axiom,(
% 6.53/1.19    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 6.53/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 6.53/1.19  fof(f780,plain,(
% 6.53/1.19    l1_pre_topc(k1_tsep_1(sK4,sK3,sK5)) | ~spl6_106),
% 6.53/1.19    inference(avatar_component_clause,[],[f778])).
% 6.53/1.19  fof(f3281,plain,(
% 6.53/1.19    ~spl6_494 | spl6_469 | ~spl6_491),
% 6.53/1.19    inference(avatar_split_clause,[],[f3276,f3260,f3149,f3278])).
% 6.53/1.19  fof(f3149,plain,(
% 6.53/1.19    spl6_469 <=> r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK3,sK5)),u1_struct_0(sK4))),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_469])])).
% 6.53/1.19  fof(f3260,plain,(
% 6.53/1.19    spl6_491 <=> u1_struct_0(k1_tsep_1(sK2,sK3,sK5)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5))),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_491])])).
% 6.53/1.19  fof(f3276,plain,(
% 6.53/1.19    ~r1_tarski(k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5)),u1_struct_0(sK4)) | (spl6_469 | ~spl6_491)),
% 6.53/1.19    inference(forward_demodulation,[],[f3151,f3262])).
% 6.53/1.19  fof(f3262,plain,(
% 6.53/1.19    u1_struct_0(k1_tsep_1(sK2,sK3,sK5)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5)) | ~spl6_491),
% 6.53/1.19    inference(avatar_component_clause,[],[f3260])).
% 6.53/1.19  fof(f3151,plain,(
% 6.53/1.19    ~r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK3,sK5)),u1_struct_0(sK4)) | spl6_469),
% 6.53/1.19    inference(avatar_component_clause,[],[f3149])).
% 6.53/1.19  fof(f3263,plain,(
% 6.53/1.19    spl6_491 | ~spl6_4 | spl6_5 | ~spl6_8 | spl6_9 | ~spl6_10 | spl6_12 | spl6_60 | ~spl6_61 | ~spl6_62),
% 6.53/1.19    inference(avatar_split_clause,[],[f2884,f468,f463,f458,f129,f119,f114,f109,f94,f89,f3260])).
% 6.53/1.19  fof(f89,plain,(
% 6.53/1.19    spl6_4 <=> m1_pre_topc(sK5,sK2)),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 6.53/1.19  fof(f109,plain,(
% 6.53/1.19    spl6_8 <=> m1_pre_topc(sK3,sK2)),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 6.53/1.19  fof(f119,plain,(
% 6.53/1.19    spl6_10 <=> l1_pre_topc(sK2)),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 6.53/1.19  fof(f129,plain,(
% 6.53/1.19    spl6_12 <=> v2_struct_0(sK2)),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 6.53/1.19  fof(f458,plain,(
% 6.53/1.19    spl6_60 <=> v2_struct_0(k1_tsep_1(sK2,sK3,sK5))),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_60])])).
% 6.53/1.19  fof(f463,plain,(
% 6.53/1.19    spl6_61 <=> v1_pre_topc(k1_tsep_1(sK2,sK3,sK5))),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_61])])).
% 6.53/1.19  fof(f468,plain,(
% 6.53/1.19    spl6_62 <=> m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK2)),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 6.53/1.19  fof(f2884,plain,(
% 6.53/1.19    u1_struct_0(k1_tsep_1(sK2,sK3,sK5)) = k2_xboole_0(u1_struct_0(sK3),u1_struct_0(sK5)) | (~spl6_4 | spl6_5 | ~spl6_8 | spl6_9 | ~spl6_10 | spl6_12 | spl6_60 | ~spl6_61 | ~spl6_62)),
% 6.53/1.19    inference(unit_resulting_resolution,[],[f131,f121,f116,f96,f111,f91,f460,f465,f470,f72])).
% 6.53/1.19  fof(f470,plain,(
% 6.53/1.19    m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK2) | ~spl6_62),
% 6.53/1.19    inference(avatar_component_clause,[],[f468])).
% 6.53/1.19  fof(f465,plain,(
% 6.53/1.19    v1_pre_topc(k1_tsep_1(sK2,sK3,sK5)) | ~spl6_61),
% 6.53/1.19    inference(avatar_component_clause,[],[f463])).
% 6.53/1.19  fof(f460,plain,(
% 6.53/1.19    ~v2_struct_0(k1_tsep_1(sK2,sK3,sK5)) | spl6_60),
% 6.53/1.19    inference(avatar_component_clause,[],[f458])).
% 6.53/1.19  fof(f91,plain,(
% 6.53/1.19    m1_pre_topc(sK5,sK2) | ~spl6_4),
% 6.53/1.19    inference(avatar_component_clause,[],[f89])).
% 6.53/1.19  fof(f111,plain,(
% 6.53/1.19    m1_pre_topc(sK3,sK2) | ~spl6_8),
% 6.53/1.19    inference(avatar_component_clause,[],[f109])).
% 6.53/1.19  fof(f121,plain,(
% 6.53/1.19    l1_pre_topc(sK2) | ~spl6_10),
% 6.53/1.19    inference(avatar_component_clause,[],[f119])).
% 6.53/1.19  fof(f131,plain,(
% 6.53/1.19    ~v2_struct_0(sK2) | spl6_12),
% 6.53/1.19    inference(avatar_component_clause,[],[f129])).
% 6.53/1.19  fof(f3152,plain,(
% 6.53/1.19    ~spl6_469 | spl6_1 | ~spl6_6 | ~spl6_10 | ~spl6_11 | ~spl6_62),
% 6.53/1.19    inference(avatar_split_clause,[],[f2908,f468,f124,f119,f99,f74,f3149])).
% 6.53/1.19  fof(f74,plain,(
% 6.53/1.19    spl6_1 <=> m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK4)),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 6.53/1.19  fof(f99,plain,(
% 6.53/1.19    spl6_6 <=> m1_pre_topc(sK4,sK2)),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 6.53/1.19  fof(f124,plain,(
% 6.53/1.19    spl6_11 <=> v2_pre_topc(sK2)),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 6.53/1.19  fof(f2908,plain,(
% 6.53/1.19    ~r1_tarski(u1_struct_0(k1_tsep_1(sK2,sK3,sK5)),u1_struct_0(sK4)) | (spl6_1 | ~spl6_6 | ~spl6_10 | ~spl6_11 | ~spl6_62)),
% 6.53/1.19    inference(unit_resulting_resolution,[],[f126,f121,f101,f76,f470,f62])).
% 6.53/1.19  fof(f62,plain,(
% 6.53/1.19    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 6.53/1.19    inference(cnf_transformation,[],[f38])).
% 6.53/1.19  fof(f76,plain,(
% 6.53/1.19    ~m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK4) | spl6_1),
% 6.53/1.19    inference(avatar_component_clause,[],[f74])).
% 6.53/1.19  fof(f101,plain,(
% 6.53/1.19    m1_pre_topc(sK4,sK2) | ~spl6_6),
% 6.53/1.19    inference(avatar_component_clause,[],[f99])).
% 6.53/1.19  fof(f126,plain,(
% 6.53/1.19    v2_pre_topc(sK2) | ~spl6_11),
% 6.53/1.19    inference(avatar_component_clause,[],[f124])).
% 6.53/1.19  fof(f818,plain,(
% 6.53/1.19    spl6_111 | ~spl6_6 | spl6_7 | ~spl6_10 | ~spl6_11 | spl6_12),
% 6.53/1.19    inference(avatar_split_clause,[],[f786,f129,f124,f119,f104,f99,f815])).
% 6.53/1.19  fof(f786,plain,(
% 6.53/1.19    m1_pre_topc(sK4,k1_tsep_1(sK2,sK4,sK4)) | (~spl6_6 | spl6_7 | ~spl6_10 | ~spl6_11 | spl6_12)),
% 6.53/1.19    inference(unit_resulting_resolution,[],[f131,f126,f121,f106,f101,f106,f101,f59])).
% 6.53/1.19  fof(f59,plain,(
% 6.53/1.19    ( ! [X2,X0,X1] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.53/1.19    inference(cnf_transformation,[],[f18])).
% 6.53/1.19  fof(f18,plain,(
% 6.53/1.19    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 6.53/1.19    inference(flattening,[],[f17])).
% 6.53/1.19  fof(f17,plain,(
% 6.53/1.19    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 6.53/1.19    inference(ennf_transformation,[],[f6])).
% 6.53/1.19  fof(f6,axiom,(
% 6.53/1.19    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))))),
% 6.53/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_tsep_1)).
% 6.53/1.19  fof(f781,plain,(
% 6.53/1.19    spl6_106 | ~spl6_14 | ~spl6_34),
% 6.53/1.19    inference(avatar_split_clause,[],[f758,f300,f147,f778])).
% 6.53/1.19  fof(f300,plain,(
% 6.53/1.19    spl6_34 <=> sP1(sK4,sK5,sK3)),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 6.53/1.19  fof(f758,plain,(
% 6.53/1.19    l1_pre_topc(k1_tsep_1(sK4,sK3,sK5)) | (~spl6_14 | ~spl6_34)),
% 6.53/1.19    inference(unit_resulting_resolution,[],[f149,f302,f166])).
% 6.53/1.19  fof(f166,plain,(
% 6.53/1.19    ( ! [X2,X0,X1] : (l1_pre_topc(k1_tsep_1(X0,X2,X1)) | ~sP1(X0,X1,X2) | ~l1_pre_topc(X0)) )),
% 6.53/1.19    inference(resolution,[],[f70,f57])).
% 6.53/1.19  fof(f57,plain,(
% 6.53/1.19    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 6.53/1.19    inference(cnf_transformation,[],[f14])).
% 6.53/1.19  fof(f14,plain,(
% 6.53/1.19    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 6.53/1.19    inference(ennf_transformation,[],[f1])).
% 6.53/1.19  fof(f1,axiom,(
% 6.53/1.19    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 6.53/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 6.53/1.19  fof(f70,plain,(
% 6.53/1.19    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X2,X1),X0) | ~sP1(X0,X1,X2)) )),
% 6.53/1.19    inference(cnf_transformation,[],[f42])).
% 6.53/1.19  fof(f42,plain,(
% 6.53/1.19    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X2,X1),X0) & v1_pre_topc(k1_tsep_1(X0,X2,X1)) & ~v2_struct_0(k1_tsep_1(X0,X2,X1))) | ~sP1(X0,X1,X2))),
% 6.53/1.19    inference(rectify,[],[f41])).
% 6.53/1.19  fof(f41,plain,(
% 6.53/1.19    ! [X0,X2,X1] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP1(X0,X2,X1))),
% 6.53/1.19    inference(nnf_transformation,[],[f29])).
% 6.53/1.19  fof(f29,plain,(
% 6.53/1.19    ! [X0,X2,X1] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP1(X0,X2,X1))),
% 6.53/1.19    introduced(predicate_definition_introduction,[new_symbols(naming,[sP1])])).
% 6.53/1.19  fof(f302,plain,(
% 6.53/1.19    sP1(sK4,sK5,sK3) | ~spl6_34),
% 6.53/1.19    inference(avatar_component_clause,[],[f300])).
% 6.53/1.19  fof(f776,plain,(
% 6.53/1.19    spl6_105 | ~spl6_34),
% 6.53/1.19    inference(avatar_split_clause,[],[f759,f300,f773])).
% 6.53/1.19  fof(f759,plain,(
% 6.53/1.19    m1_pre_topc(k1_tsep_1(sK4,sK3,sK5),sK4) | ~spl6_34),
% 6.53/1.19    inference(unit_resulting_resolution,[],[f302,f70])).
% 6.53/1.19  fof(f771,plain,(
% 6.53/1.19    spl6_104 | ~spl6_34),
% 6.53/1.19    inference(avatar_split_clause,[],[f760,f300,f768])).
% 6.53/1.19  fof(f760,plain,(
% 6.53/1.19    v1_pre_topc(k1_tsep_1(sK4,sK3,sK5)) | ~spl6_34),
% 6.53/1.19    inference(unit_resulting_resolution,[],[f302,f69])).
% 6.53/1.19  fof(f69,plain,(
% 6.53/1.19    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X2,X1)) | ~sP1(X0,X1,X2)) )),
% 6.53/1.19    inference(cnf_transformation,[],[f42])).
% 6.53/1.19  fof(f766,plain,(
% 6.53/1.19    ~spl6_103 | ~spl6_34),
% 6.53/1.19    inference(avatar_split_clause,[],[f761,f300,f763])).
% 6.53/1.19  fof(f761,plain,(
% 6.53/1.19    ~v2_struct_0(k1_tsep_1(sK4,sK3,sK5)) | ~spl6_34),
% 6.53/1.19    inference(unit_resulting_resolution,[],[f302,f68])).
% 6.53/1.19  fof(f68,plain,(
% 6.53/1.19    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X2,X1)) | ~sP1(X0,X1,X2)) )),
% 6.53/1.19    inference(cnf_transformation,[],[f42])).
% 6.53/1.19  fof(f648,plain,(
% 6.53/1.19    spl6_87 | ~spl6_6 | spl6_7 | ~spl6_10 | ~spl6_11 | spl6_12),
% 6.53/1.19    inference(avatar_split_clause,[],[f620,f129,f124,f119,f104,f99,f645])).
% 6.53/1.19  fof(f620,plain,(
% 6.53/1.19    g1_pre_topc(u1_struct_0(sK4),u1_pre_topc(sK4)) = k1_tsep_1(sK2,sK4,sK4) | (~spl6_6 | spl6_7 | ~spl6_10 | ~spl6_11 | spl6_12)),
% 6.53/1.19    inference(unit_resulting_resolution,[],[f131,f126,f121,f106,f101,f58])).
% 6.53/1.19  fof(f58,plain,(
% 6.53/1.19    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.53/1.19    inference(cnf_transformation,[],[f16])).
% 6.53/1.19  fof(f16,plain,(
% 6.53/1.19    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 6.53/1.19    inference(flattening,[],[f15])).
% 6.53/1.19  fof(f15,plain,(
% 6.53/1.19    ! [X0] : (! [X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 6.53/1.19    inference(ennf_transformation,[],[f7])).
% 6.53/1.19  fof(f7,axiom,(
% 6.53/1.19    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) = k1_tsep_1(X0,X1,X1)))),
% 6.53/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_tmap_1)).
% 6.53/1.19  fof(f618,plain,(
% 6.53/1.19    spl6_85 | ~spl6_68),
% 6.53/1.19    inference(avatar_split_clause,[],[f611,f507,f615])).
% 6.53/1.19  fof(f507,plain,(
% 6.53/1.19    spl6_68 <=> sP0(sK4,sK4,sK2)),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_68])])).
% 6.53/1.19  fof(f611,plain,(
% 6.53/1.19    v2_pre_topc(k1_tsep_1(sK2,sK4,sK4)) | ~spl6_68),
% 6.53/1.19    inference(unit_resulting_resolution,[],[f509,f66])).
% 6.53/1.19  fof(f66,plain,(
% 6.53/1.19    ( ! [X2,X0,X1] : (v2_pre_topc(k1_tsep_1(X2,X1,X0)) | ~sP0(X0,X1,X2)) )),
% 6.53/1.19    inference(cnf_transformation,[],[f40])).
% 6.53/1.19  fof(f40,plain,(
% 6.53/1.19    ! [X0,X1,X2] : ((v2_pre_topc(k1_tsep_1(X2,X1,X0)) & v1_pre_topc(k1_tsep_1(X2,X1,X0)) & ~v2_struct_0(k1_tsep_1(X2,X1,X0))) | ~sP0(X0,X1,X2))),
% 6.53/1.19    inference(rectify,[],[f39])).
% 6.53/1.19  fof(f39,plain,(
% 6.53/1.19    ! [X2,X1,X0] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP0(X2,X1,X0))),
% 6.53/1.19    inference(nnf_transformation,[],[f27])).
% 6.53/1.19  fof(f27,plain,(
% 6.53/1.19    ! [X2,X1,X0] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP0(X2,X1,X0))),
% 6.53/1.19    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 6.53/1.19  fof(f509,plain,(
% 6.53/1.19    sP0(sK4,sK4,sK2) | ~spl6_68),
% 6.53/1.19    inference(avatar_component_clause,[],[f507])).
% 6.53/1.19  fof(f510,plain,(
% 6.53/1.19    spl6_68 | ~spl6_6 | spl6_7 | ~spl6_10 | ~spl6_11 | spl6_12),
% 6.53/1.19    inference(avatar_split_clause,[],[f481,f129,f124,f119,f104,f99,f507])).
% 6.53/1.19  fof(f481,plain,(
% 6.53/1.19    sP0(sK4,sK4,sK2) | (~spl6_6 | spl6_7 | ~spl6_10 | ~spl6_11 | spl6_12)),
% 6.53/1.19    inference(unit_resulting_resolution,[],[f131,f126,f121,f106,f101,f106,f101,f67])).
% 6.53/1.19  fof(f67,plain,(
% 6.53/1.19    ( ! [X2,X0,X1] : (sP0(X2,X1,X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.53/1.19    inference(cnf_transformation,[],[f28])).
% 6.53/1.19  fof(f28,plain,(
% 6.53/1.19    ! [X0,X1,X2] : (sP0(X2,X1,X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 6.53/1.19    inference(definition_folding,[],[f24,f27])).
% 6.53/1.19  fof(f24,plain,(
% 6.53/1.19    ! [X0,X1,X2] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 6.53/1.19    inference(flattening,[],[f23])).
% 6.53/1.19  fof(f23,plain,(
% 6.53/1.19    ! [X0,X1,X2] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 6.53/1.19    inference(ennf_transformation,[],[f5])).
% 6.53/1.19  fof(f5,axiom,(
% 6.53/1.19    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 6.53/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tmap_1)).
% 6.53/1.19  fof(f471,plain,(
% 6.53/1.19    spl6_62 | ~spl6_29),
% 6.53/1.19    inference(avatar_split_clause,[],[f454,f275,f468])).
% 6.53/1.19  fof(f275,plain,(
% 6.53/1.19    spl6_29 <=> sP1(sK2,sK5,sK3)),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 6.53/1.19  fof(f454,plain,(
% 6.53/1.19    m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK2) | ~spl6_29),
% 6.53/1.19    inference(unit_resulting_resolution,[],[f277,f70])).
% 6.53/1.19  fof(f277,plain,(
% 6.53/1.19    sP1(sK2,sK5,sK3) | ~spl6_29),
% 6.53/1.19    inference(avatar_component_clause,[],[f275])).
% 6.53/1.19  fof(f466,plain,(
% 6.53/1.19    spl6_61 | ~spl6_29),
% 6.53/1.19    inference(avatar_split_clause,[],[f455,f275,f463])).
% 6.53/1.19  fof(f455,plain,(
% 6.53/1.19    v1_pre_topc(k1_tsep_1(sK2,sK3,sK5)) | ~spl6_29),
% 6.53/1.19    inference(unit_resulting_resolution,[],[f277,f69])).
% 6.53/1.19  fof(f461,plain,(
% 6.53/1.19    ~spl6_60 | ~spl6_29),
% 6.53/1.19    inference(avatar_split_clause,[],[f456,f275,f458])).
% 6.53/1.19  fof(f456,plain,(
% 6.53/1.19    ~v2_struct_0(k1_tsep_1(sK2,sK3,sK5)) | ~spl6_29),
% 6.53/1.19    inference(unit_resulting_resolution,[],[f277,f68])).
% 6.53/1.19  fof(f428,plain,(
% 6.53/1.19    spl6_55 | ~spl6_10 | ~spl6_27),
% 6.53/1.19    inference(avatar_split_clause,[],[f405,f265,f119,f425])).
% 6.53/1.19  fof(f265,plain,(
% 6.53/1.19    spl6_27 <=> sP1(sK2,sK4,sK4)),
% 6.53/1.19    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 6.53/1.19  fof(f405,plain,(
% 6.53/1.19    l1_pre_topc(k1_tsep_1(sK2,sK4,sK4)) | (~spl6_10 | ~spl6_27)),
% 6.53/1.19    inference(unit_resulting_resolution,[],[f121,f267,f166])).
% 6.53/1.19  fof(f267,plain,(
% 6.53/1.19    sP1(sK2,sK4,sK4) | ~spl6_27),
% 6.53/1.19    inference(avatar_component_clause,[],[f265])).
% 6.53/1.19  fof(f303,plain,(
% 6.53/1.19    spl6_34 | ~spl6_2 | ~spl6_3 | spl6_5 | spl6_7 | spl6_9 | ~spl6_14),
% 6.53/1.19    inference(avatar_split_clause,[],[f232,f147,f114,f104,f94,f84,f79,f300])).
% 6.53/1.19  fof(f232,plain,(
% 6.53/1.19    sP1(sK4,sK5,sK3) | (~spl6_2 | ~spl6_3 | spl6_5 | spl6_7 | spl6_9 | ~spl6_14)),
% 6.53/1.19    inference(unit_resulting_resolution,[],[f106,f149,f116,f86,f96,f81,f71])).
% 6.53/1.19  fof(f71,plain,(
% 6.53/1.19    ( ! [X2,X0,X1] : (sP1(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 6.53/1.19    inference(cnf_transformation,[],[f30])).
% 6.53/1.19  fof(f30,plain,(
% 6.53/1.19    ! [X0,X1,X2] : (sP1(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 6.53/1.19    inference(definition_folding,[],[f26,f29])).
% 6.53/1.19  fof(f26,plain,(
% 6.53/1.19    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 6.53/1.19    inference(flattening,[],[f25])).
% 6.53/1.19  fof(f25,plain,(
% 6.53/1.19    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 6.53/1.19    inference(ennf_transformation,[],[f4])).
% 6.53/1.19  fof(f4,axiom,(
% 6.53/1.19    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 6.53/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 6.53/1.19  fof(f278,plain,(
% 6.53/1.19    spl6_29 | ~spl6_4 | spl6_5 | ~spl6_8 | spl6_9 | ~spl6_10 | spl6_12),
% 6.53/1.19    inference(avatar_split_clause,[],[f237,f129,f119,f114,f109,f94,f89,f275])).
% 6.53/1.19  fof(f237,plain,(
% 6.53/1.19    sP1(sK2,sK5,sK3) | (~spl6_4 | spl6_5 | ~spl6_8 | spl6_9 | ~spl6_10 | spl6_12)),
% 6.53/1.19    inference(unit_resulting_resolution,[],[f131,f121,f116,f111,f96,f91,f71])).
% 6.53/1.19  fof(f268,plain,(
% 6.53/1.19    spl6_27 | ~spl6_6 | spl6_7 | ~spl6_10 | spl6_12),
% 6.53/1.19    inference(avatar_split_clause,[],[f239,f129,f119,f104,f99,f265])).
% 6.53/1.19  fof(f239,plain,(
% 6.53/1.19    sP1(sK2,sK4,sK4) | (~spl6_6 | spl6_7 | ~spl6_10 | spl6_12)),
% 6.53/1.19    inference(unit_resulting_resolution,[],[f131,f121,f106,f101,f106,f101,f71])).
% 6.53/1.19  fof(f161,plain,(
% 6.53/1.19    spl6_14 | ~spl6_6 | ~spl6_10),
% 6.53/1.19    inference(avatar_split_clause,[],[f160,f119,f99,f147])).
% 6.53/1.19  fof(f160,plain,(
% 6.53/1.19    l1_pre_topc(sK4) | (~spl6_6 | ~spl6_10)),
% 6.53/1.19    inference(subsumption_resolution,[],[f139,f121])).
% 6.53/1.19  fof(f139,plain,(
% 6.53/1.19    l1_pre_topc(sK4) | ~l1_pre_topc(sK2) | ~spl6_6),
% 6.53/1.19    inference(resolution,[],[f57,f101])).
% 6.53/1.19  fof(f132,plain,(
% 6.53/1.19    ~spl6_12),
% 6.53/1.19    inference(avatar_split_clause,[],[f43,f129])).
% 6.53/1.19  fof(f43,plain,(
% 6.53/1.19    ~v2_struct_0(sK2)),
% 6.53/1.19    inference(cnf_transformation,[],[f35])).
% 6.53/1.19  fof(f35,plain,(
% 6.53/1.19    (((~m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK4) & m1_pre_topc(sK5,sK4) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2)),
% 6.53/1.19    inference(skolemisation,[status(esa),new_symbols(skolem,[sK2,sK3,sK4,sK5])],[f12,f34,f33,f32,f31])).
% 6.53/1.19  fof(f31,plain,(
% 6.53/1.19    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK2,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) & l1_pre_topc(sK2) & v2_pre_topc(sK2) & ~v2_struct_0(sK2))),
% 6.53/1.19    introduced(choice_axiom,[])).
% 6.53/1.19  fof(f32,plain,(
% 6.53/1.19    ? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK2,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK2) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK2,sK3,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK3,X2) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) & m1_pre_topc(sK3,sK2) & ~v2_struct_0(sK3))),
% 6.53/1.19    introduced(choice_axiom,[])).
% 6.53/1.19  fof(f33,plain,(
% 6.53/1.19    ? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK2,sK3,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK3,X2) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK2) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k1_tsep_1(sK2,sK3,X3),sK4) & m1_pre_topc(X3,sK4) & m1_pre_topc(sK3,sK4) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) & m1_pre_topc(sK4,sK2) & ~v2_struct_0(sK4))),
% 6.53/1.19    introduced(choice_axiom,[])).
% 6.53/1.19  fof(f34,plain,(
% 6.53/1.19    ? [X3] : (~m1_pre_topc(k1_tsep_1(sK2,sK3,X3),sK4) & m1_pre_topc(X3,sK4) & m1_pre_topc(sK3,sK4) & m1_pre_topc(X3,sK2) & ~v2_struct_0(X3)) => (~m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK4) & m1_pre_topc(sK5,sK4) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK5,sK2) & ~v2_struct_0(sK5))),
% 6.53/1.19    introduced(choice_axiom,[])).
% 6.53/1.19  fof(f12,plain,(
% 6.53/1.19    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 6.53/1.19    inference(flattening,[],[f11])).
% 6.53/1.19  fof(f11,plain,(
% 6.53/1.19    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & (m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 6.53/1.19    inference(ennf_transformation,[],[f10])).
% 6.53/1.19  fof(f10,negated_conjecture,(
% 6.53/1.19    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 6.53/1.19    inference(negated_conjecture,[],[f9])).
% 6.53/1.19  fof(f9,conjecture,(
% 6.53/1.19    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 6.53/1.19    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tmap_1)).
% 6.53/1.19  fof(f127,plain,(
% 6.53/1.19    spl6_11),
% 6.53/1.19    inference(avatar_split_clause,[],[f44,f124])).
% 6.53/1.19  fof(f44,plain,(
% 6.53/1.19    v2_pre_topc(sK2)),
% 6.53/1.19    inference(cnf_transformation,[],[f35])).
% 6.53/1.19  fof(f122,plain,(
% 6.53/1.19    spl6_10),
% 6.53/1.19    inference(avatar_split_clause,[],[f45,f119])).
% 6.53/1.19  fof(f45,plain,(
% 6.53/1.19    l1_pre_topc(sK2)),
% 6.53/1.19    inference(cnf_transformation,[],[f35])).
% 6.53/1.19  fof(f117,plain,(
% 6.53/1.19    ~spl6_9),
% 6.53/1.19    inference(avatar_split_clause,[],[f46,f114])).
% 6.53/1.19  fof(f46,plain,(
% 6.53/1.19    ~v2_struct_0(sK3)),
% 6.53/1.19    inference(cnf_transformation,[],[f35])).
% 6.53/1.19  fof(f112,plain,(
% 6.53/1.19    spl6_8),
% 6.53/1.19    inference(avatar_split_clause,[],[f47,f109])).
% 6.53/1.19  fof(f47,plain,(
% 6.53/1.19    m1_pre_topc(sK3,sK2)),
% 6.53/1.19    inference(cnf_transformation,[],[f35])).
% 6.53/1.19  fof(f107,plain,(
% 6.53/1.19    ~spl6_7),
% 6.53/1.19    inference(avatar_split_clause,[],[f48,f104])).
% 6.53/1.19  fof(f48,plain,(
% 6.53/1.19    ~v2_struct_0(sK4)),
% 6.53/1.19    inference(cnf_transformation,[],[f35])).
% 6.53/1.19  fof(f102,plain,(
% 6.53/1.19    spl6_6),
% 6.53/1.19    inference(avatar_split_clause,[],[f49,f99])).
% 6.53/1.19  fof(f49,plain,(
% 6.53/1.19    m1_pre_topc(sK4,sK2)),
% 6.53/1.19    inference(cnf_transformation,[],[f35])).
% 6.53/1.19  fof(f97,plain,(
% 6.53/1.19    ~spl6_5),
% 6.53/1.19    inference(avatar_split_clause,[],[f50,f94])).
% 6.53/1.19  fof(f50,plain,(
% 6.53/1.19    ~v2_struct_0(sK5)),
% 6.53/1.19    inference(cnf_transformation,[],[f35])).
% 6.53/1.19  fof(f92,plain,(
% 6.53/1.19    spl6_4),
% 6.53/1.19    inference(avatar_split_clause,[],[f51,f89])).
% 6.53/1.19  fof(f51,plain,(
% 6.53/1.19    m1_pre_topc(sK5,sK2)),
% 6.53/1.19    inference(cnf_transformation,[],[f35])).
% 6.53/1.19  fof(f87,plain,(
% 6.53/1.19    spl6_3),
% 6.53/1.19    inference(avatar_split_clause,[],[f52,f84])).
% 6.53/1.19  fof(f52,plain,(
% 6.53/1.19    m1_pre_topc(sK3,sK4)),
% 6.53/1.19    inference(cnf_transformation,[],[f35])).
% 6.53/1.19  fof(f82,plain,(
% 6.53/1.19    spl6_2),
% 6.53/1.19    inference(avatar_split_clause,[],[f53,f79])).
% 6.53/1.19  fof(f53,plain,(
% 6.53/1.19    m1_pre_topc(sK5,sK4)),
% 6.53/1.19    inference(cnf_transformation,[],[f35])).
% 6.53/1.19  fof(f77,plain,(
% 6.53/1.19    ~spl6_1),
% 6.53/1.19    inference(avatar_split_clause,[],[f54,f74])).
% 6.53/1.19  fof(f54,plain,(
% 6.53/1.19    ~m1_pre_topc(k1_tsep_1(sK2,sK3,sK5),sK4)),
% 6.53/1.19    inference(cnf_transformation,[],[f35])).
% 6.53/1.19  % SZS output end Proof for theBenchmark
% 6.53/1.19  % (13241)------------------------------
% 6.53/1.19  % (13241)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 6.53/1.19  % (13241)Termination reason: Refutation
% 6.53/1.19  
% 6.53/1.19  % (13241)Memory used [KB]: 23027
% 6.53/1.19  % (13241)Time elapsed: 0.763 s
% 6.53/1.19  % (13241)------------------------------
% 6.53/1.19  % (13241)------------------------------
% 6.53/1.20  % (13221)Success in time 0.846 s
%------------------------------------------------------------------------------
