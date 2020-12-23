%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:03 EST 2020

% Result     : Theorem 1.63s
% Output     : Refutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :  167 ( 447 expanded)
%              Number of leaves         :   40 ( 218 expanded)
%              Depth                    :   10
%              Number of atoms          :  717 (2603 expanded)
%              Number of equality atoms :   31 (  47 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2521,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f67,f72,f77,f82,f87,f92,f97,f102,f107,f112,f117,f122,f151,f188,f260,f285,f536,f541,f546,f719,f724,f729,f1362,f1378,f1390,f1929,f2361,f2507])).

fof(f2507,plain,
    ( ~ spl5_14
    | ~ spl5_17
    | ~ spl5_98
    | spl5_183
    | ~ spl5_259
    | ~ spl5_315 ),
    inference(avatar_contradiction_clause,[],[f2506])).

fof(f2506,plain,
    ( $false
    | ~ spl5_14
    | ~ spl5_17
    | ~ spl5_98
    | spl5_183
    | ~ spl5_259
    | ~ spl5_315 ),
    inference(subsumption_resolution,[],[f2505,f1389])).

fof(f1389,plain,
    ( ~ r1_tarski(k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)),u1_struct_0(sK3))
    | spl5_183 ),
    inference(avatar_component_clause,[],[f1387])).

fof(f1387,plain,
    ( spl5_183
  <=> r1_tarski(k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_183])])).

fof(f2505,plain,
    ( r1_tarski(k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)),u1_struct_0(sK3))
    | ~ spl5_14
    | ~ spl5_17
    | ~ spl5_98
    | ~ spl5_259
    | ~ spl5_315 ),
    inference(forward_demodulation,[],[f2407,f1928])).

fof(f1928,plain,
    ( k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)) = u1_struct_0(k1_tsep_1(sK3,sK2,sK4))
    | ~ spl5_259 ),
    inference(avatar_component_clause,[],[f1926])).

fof(f1926,plain,
    ( spl5_259
  <=> k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)) = u1_struct_0(k1_tsep_1(sK3,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_259])])).

fof(f2407,plain,
    ( r1_tarski(u1_struct_0(k1_tsep_1(sK3,sK2,sK4)),u1_struct_0(sK3))
    | ~ spl5_14
    | ~ spl5_17
    | ~ spl5_98
    | ~ spl5_315 ),
    inference(unit_resulting_resolution,[],[f172,f139,f728,f728,f2360,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f2360,plain,
    ( m1_pre_topc(sK3,sK3)
    | ~ spl5_315 ),
    inference(avatar_component_clause,[],[f2358])).

fof(f2358,plain,
    ( spl5_315
  <=> m1_pre_topc(sK3,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_315])])).

fof(f728,plain,
    ( m1_pre_topc(k1_tsep_1(sK3,sK2,sK4),sK3)
    | ~ spl5_98 ),
    inference(avatar_component_clause,[],[f726])).

fof(f726,plain,
    ( spl5_98
  <=> m1_pre_topc(k1_tsep_1(sK3,sK2,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f139,plain,
    ( l1_pre_topc(sK3)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f137])).

fof(f137,plain,
    ( spl5_14
  <=> l1_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f172,plain,
    ( v2_pre_topc(sK3)
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl5_17
  <=> v2_pre_topc(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f2361,plain,
    ( spl5_315
    | ~ spl5_6
    | spl5_7
    | ~ spl5_10
    | ~ spl5_11
    | spl5_12 ),
    inference(avatar_split_clause,[],[f2321,f119,f114,f109,f94,f89,f2358])).

fof(f89,plain,
    ( spl5_6
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f94,plain,
    ( spl5_7
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f109,plain,
    ( spl5_10
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f114,plain,
    ( spl5_11
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f119,plain,
    ( spl5_12
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f2321,plain,
    ( m1_pre_topc(sK3,sK3)
    | ~ spl5_6
    | spl5_7
    | ~ spl5_10
    | ~ spl5_11
    | spl5_12 ),
    inference(unit_resulting_resolution,[],[f121,f116,f111,f96,f91,f763])).

fof(f763,plain,(
    ! [X0,X1] :
      ( m1_pre_topc(X1,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(trivial_inequality_removal,[],[f762])).

fof(f762,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | m1_pre_topc(X1,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f755])).

fof(f755,plain,(
    ! [X0,X1] :
      ( g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | m1_pre_topc(X1,X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(superposition,[],[f52,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
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
         => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X2)
                  | k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
                & ( k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))
                  | ~ m1_pre_topc(X1,X2) ) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(nnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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
             => ( m1_pre_topc(X1,X2)
              <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).

fof(f91,plain,
    ( m1_pre_topc(sK3,sK1)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f96,plain,
    ( ~ v2_struct_0(sK3)
    | spl5_7 ),
    inference(avatar_component_clause,[],[f94])).

fof(f111,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f109])).

fof(f116,plain,
    ( v2_pre_topc(sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f114])).

fof(f121,plain,
    ( ~ v2_struct_0(sK1)
    | spl5_12 ),
    inference(avatar_component_clause,[],[f119])).

fof(f1929,plain,
    ( spl5_259
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | spl5_9
    | ~ spl5_14
    | spl5_96
    | ~ spl5_97
    | ~ spl5_98 ),
    inference(avatar_split_clause,[],[f1858,f726,f721,f716,f137,f104,f94,f84,f74,f69,f1926])).

fof(f69,plain,
    ( spl5_2
  <=> m1_pre_topc(sK4,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f74,plain,
    ( spl5_3
  <=> m1_pre_topc(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f84,plain,
    ( spl5_5
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f104,plain,
    ( spl5_9
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f716,plain,
    ( spl5_96
  <=> v2_struct_0(k1_tsep_1(sK3,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).

fof(f721,plain,
    ( spl5_97
  <=> v1_pre_topc(k1_tsep_1(sK3,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).

fof(f1858,plain,
    ( k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)) = u1_struct_0(k1_tsep_1(sK3,sK2,sK4))
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | spl5_9
    | ~ spl5_14
    | spl5_96
    | ~ spl5_97
    | ~ spl5_98 ),
    inference(unit_resulting_resolution,[],[f96,f139,f106,f86,f76,f71,f718,f723,f728,f62])).

fof(f62,plain,(
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
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(nnf_transformation,[],[f18])).

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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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

fof(f723,plain,
    ( v1_pre_topc(k1_tsep_1(sK3,sK2,sK4))
    | ~ spl5_97 ),
    inference(avatar_component_clause,[],[f721])).

fof(f718,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK3,sK2,sK4))
    | spl5_96 ),
    inference(avatar_component_clause,[],[f716])).

fof(f71,plain,
    ( m1_pre_topc(sK4,sK3)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f69])).

fof(f76,plain,
    ( m1_pre_topc(sK2,sK3)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f74])).

fof(f86,plain,
    ( ~ v2_struct_0(sK4)
    | spl5_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f106,plain,
    ( ~ v2_struct_0(sK2)
    | spl5_9 ),
    inference(avatar_component_clause,[],[f104])).

fof(f1390,plain,
    ( ~ spl5_183
    | spl5_178
    | ~ spl5_181 ),
    inference(avatar_split_clause,[],[f1385,f1375,f1359,f1387])).

fof(f1359,plain,
    ( spl5_178
  <=> r1_tarski(u1_struct_0(k1_tsep_1(sK1,sK2,sK4)),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_178])])).

fof(f1375,plain,
    ( spl5_181
  <=> u1_struct_0(k1_tsep_1(sK1,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_181])])).

fof(f1385,plain,
    ( ~ r1_tarski(k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)),u1_struct_0(sK3))
    | spl5_178
    | ~ spl5_181 ),
    inference(forward_demodulation,[],[f1361,f1377])).

fof(f1377,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4))
    | ~ spl5_181 ),
    inference(avatar_component_clause,[],[f1375])).

fof(f1361,plain,
    ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK1,sK2,sK4)),u1_struct_0(sK3))
    | spl5_178 ),
    inference(avatar_component_clause,[],[f1359])).

fof(f1378,plain,
    ( spl5_181
    | ~ spl5_4
    | spl5_5
    | ~ spl5_8
    | spl5_9
    | ~ spl5_10
    | spl5_12
    | spl5_71
    | ~ spl5_72
    | ~ spl5_73 ),
    inference(avatar_split_clause,[],[f1258,f543,f538,f533,f119,f109,f104,f99,f84,f79,f1375])).

fof(f79,plain,
    ( spl5_4
  <=> m1_pre_topc(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f99,plain,
    ( spl5_8
  <=> m1_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f533,plain,
    ( spl5_71
  <=> v2_struct_0(k1_tsep_1(sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).

fof(f538,plain,
    ( spl5_72
  <=> v1_pre_topc(k1_tsep_1(sK1,sK2,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f543,plain,
    ( spl5_73
  <=> m1_pre_topc(k1_tsep_1(sK1,sK2,sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).

fof(f1258,plain,
    ( u1_struct_0(k1_tsep_1(sK1,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4))
    | ~ spl5_4
    | spl5_5
    | ~ spl5_8
    | spl5_9
    | ~ spl5_10
    | spl5_12
    | spl5_71
    | ~ spl5_72
    | ~ spl5_73 ),
    inference(unit_resulting_resolution,[],[f121,f111,f106,f86,f101,f81,f535,f540,f545,f62])).

fof(f545,plain,
    ( m1_pre_topc(k1_tsep_1(sK1,sK2,sK4),sK1)
    | ~ spl5_73 ),
    inference(avatar_component_clause,[],[f543])).

fof(f540,plain,
    ( v1_pre_topc(k1_tsep_1(sK1,sK2,sK4))
    | ~ spl5_72 ),
    inference(avatar_component_clause,[],[f538])).

fof(f535,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK1,sK2,sK4))
    | spl5_71 ),
    inference(avatar_component_clause,[],[f533])).

fof(f81,plain,
    ( m1_pre_topc(sK4,sK1)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f79])).

fof(f101,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ spl5_8 ),
    inference(avatar_component_clause,[],[f99])).

fof(f1362,plain,
    ( ~ spl5_178
    | spl5_1
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_73 ),
    inference(avatar_split_clause,[],[f1263,f543,f114,f109,f89,f64,f1359])).

fof(f64,plain,
    ( spl5_1
  <=> m1_pre_topc(k1_tsep_1(sK1,sK2,sK4),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1263,plain,
    ( ~ r1_tarski(u1_struct_0(k1_tsep_1(sK1,sK2,sK4)),u1_struct_0(sK3))
    | spl5_1
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_11
    | ~ spl5_73 ),
    inference(unit_resulting_resolution,[],[f116,f111,f91,f66,f545,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f66,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK1,sK2,sK4),sK3)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f64])).

fof(f729,plain,
    ( spl5_98
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f712,f282,f726])).

fof(f282,plain,
    ( spl5_32
  <=> sP0(sK3,sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f712,plain,
    ( m1_pre_topc(k1_tsep_1(sK3,sK2,sK4),sK3)
    | ~ spl5_32 ),
    inference(unit_resulting_resolution,[],[f284,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X2,X1),X0)
        & v1_pre_topc(k1_tsep_1(X0,X2,X1))
        & ~ v2_struct_0(k1_tsep_1(X0,X2,X1)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f35])).

fof(f35,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k1_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k1_tsep_1(X0,X1,X2)) )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f284,plain,
    ( sP0(sK3,sK4,sK2)
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f282])).

fof(f724,plain,
    ( spl5_97
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f713,f282,f721])).

fof(f713,plain,
    ( v1_pre_topc(k1_tsep_1(sK3,sK2,sK4))
    | ~ spl5_32 ),
    inference(unit_resulting_resolution,[],[f284,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k1_tsep_1(X0,X2,X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f719,plain,
    ( ~ spl5_96
    | ~ spl5_32 ),
    inference(avatar_split_clause,[],[f714,f282,f716])).

fof(f714,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK3,sK2,sK4))
    | ~ spl5_32 ),
    inference(unit_resulting_resolution,[],[f284,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X2,X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f546,plain,
    ( spl5_73
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f529,f257,f543])).

fof(f257,plain,
    ( spl5_27
  <=> sP0(sK1,sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).

fof(f529,plain,
    ( m1_pre_topc(k1_tsep_1(sK1,sK2,sK4),sK1)
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f259,f60])).

fof(f259,plain,
    ( sP0(sK1,sK4,sK2)
    | ~ spl5_27 ),
    inference(avatar_component_clause,[],[f257])).

fof(f541,plain,
    ( spl5_72
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f530,f257,f538])).

fof(f530,plain,
    ( v1_pre_topc(k1_tsep_1(sK1,sK2,sK4))
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f259,f59])).

fof(f536,plain,
    ( ~ spl5_71
    | ~ spl5_27 ),
    inference(avatar_split_clause,[],[f531,f257,f533])).

fof(f531,plain,
    ( ~ v2_struct_0(k1_tsep_1(sK1,sK2,sK4))
    | ~ spl5_27 ),
    inference(unit_resulting_resolution,[],[f259,f58])).

fof(f285,plain,
    ( spl5_32
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | spl5_9
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f214,f137,f104,f94,f84,f74,f69,f282])).

fof(f214,plain,
    ( sP0(sK3,sK4,sK2)
    | ~ spl5_2
    | ~ spl5_3
    | spl5_5
    | spl5_7
    | spl5_9
    | ~ spl5_14 ),
    inference(unit_resulting_resolution,[],[f96,f139,f106,f76,f86,f71,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( sP0(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f24,f25])).

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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f260,plain,
    ( spl5_27
    | ~ spl5_4
    | spl5_5
    | ~ spl5_8
    | spl5_9
    | ~ spl5_10
    | spl5_12 ),
    inference(avatar_split_clause,[],[f219,f119,f109,f104,f99,f84,f79,f257])).

fof(f219,plain,
    ( sP0(sK1,sK4,sK2)
    | ~ spl5_4
    | spl5_5
    | ~ spl5_8
    | spl5_9
    | ~ spl5_10
    | spl5_12 ),
    inference(unit_resulting_resolution,[],[f121,f111,f106,f101,f86,f81,f61])).

fof(f188,plain,
    ( spl5_17
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f187,f114,f109,f89,f170])).

fof(f187,plain,
    ( v2_pre_topc(sK3)
    | ~ spl5_6
    | ~ spl5_10
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f186,f116])).

fof(f186,plain,
    ( v2_pre_topc(sK3)
    | ~ v2_pre_topc(sK1)
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f162,f111])).

fof(f162,plain,
    ( v2_pre_topc(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl5_6 ),
    inference(resolution,[],[f55,f91])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f151,plain,
    ( spl5_14
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f150,f109,f89,f137])).

fof(f150,plain,
    ( l1_pre_topc(sK3)
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f129,f111])).

fof(f129,plain,
    ( l1_pre_topc(sK3)
    | ~ l1_pre_topc(sK1)
    | ~ spl5_6 ),
    inference(resolution,[],[f49,f91])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f122,plain,(
    ~ spl5_12 ),
    inference(avatar_split_clause,[],[f37,f119])).

fof(f37,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( ~ m1_pre_topc(k1_tsep_1(sK1,sK2,sK4),sK3)
    & m1_pre_topc(sK4,sK3)
    & m1_pre_topc(sK2,sK3)
    & m1_pre_topc(sK4,sK1)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f11,f30,f29,f28,f27])).

fof(f27,plain,
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
                  ( ~ m1_pre_topc(k1_tsep_1(sK1,X1,X3),X2)
                  & m1_pre_topc(X3,X2)
                  & m1_pre_topc(X1,X2)
                  & m1_pre_topc(X3,sK1)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK1)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK1)
      & v2_pre_topc(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_pre_topc(k1_tsep_1(sK1,X1,X3),X2)
                & m1_pre_topc(X3,X2)
                & m1_pre_topc(X1,X2)
                & m1_pre_topc(X3,sK1)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK1)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_pre_topc(k1_tsep_1(sK1,sK2,X3),X2)
              & m1_pre_topc(X3,X2)
              & m1_pre_topc(sK2,X2)
              & m1_pre_topc(X3,sK1)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK1)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK2,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f29,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_pre_topc(k1_tsep_1(sK1,sK2,X3),X2)
            & m1_pre_topc(X3,X2)
            & m1_pre_topc(sK2,X2)
            & m1_pre_topc(X3,sK1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK1)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ m1_pre_topc(k1_tsep_1(sK1,sK2,X3),sK3)
          & m1_pre_topc(X3,sK3)
          & m1_pre_topc(sK2,sK3)
          & m1_pre_topc(X3,sK1)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK3,sK1)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f30,plain,
    ( ? [X3] :
        ( ~ m1_pre_topc(k1_tsep_1(sK1,sK2,X3),sK3)
        & m1_pre_topc(X3,sK3)
        & m1_pre_topc(sK2,sK3)
        & m1_pre_topc(X3,sK1)
        & ~ v2_struct_0(X3) )
   => ( ~ m1_pre_topc(k1_tsep_1(sK1,sK2,sK4),sK3)
      & m1_pre_topc(sK4,sK3)
      & m1_pre_topc(sK2,sK3)
      & m1_pre_topc(sK4,sK1)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
                   => ( ( m1_pre_topc(X3,X2)
                        & m1_pre_topc(X1,X2) )
                     => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
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
                 => ( ( m1_pre_topc(X3,X2)
                      & m1_pre_topc(X1,X2) )
                   => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tmap_1)).

fof(f117,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f38,f114])).

fof(f38,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f112,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f39,f109])).

fof(f39,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f107,plain,(
    ~ spl5_9 ),
    inference(avatar_split_clause,[],[f40,f104])).

fof(f40,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f31])).

fof(f102,plain,(
    spl5_8 ),
    inference(avatar_split_clause,[],[f41,f99])).

fof(f41,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f97,plain,(
    ~ spl5_7 ),
    inference(avatar_split_clause,[],[f42,f94])).

fof(f42,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f92,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f43,f89])).

fof(f43,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f87,plain,(
    ~ spl5_5 ),
    inference(avatar_split_clause,[],[f44,f84])).

fof(f44,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f31])).

fof(f82,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f45,f79])).

fof(f45,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f31])).

fof(f77,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f46,f74])).

fof(f46,plain,(
    m1_pre_topc(sK2,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f72,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f47,f69])).

fof(f47,plain,(
    m1_pre_topc(sK4,sK3) ),
    inference(cnf_transformation,[],[f31])).

fof(f67,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f48,f64])).

fof(f48,plain,(
    ~ m1_pre_topc(k1_tsep_1(sK1,sK2,sK4),sK3) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.32  % Computer   : n005.cluster.edu
% 0.13/0.32  % Model      : x86_64 x86_64
% 0.13/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.32  % Memory     : 8042.1875MB
% 0.13/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.32  % CPULimit   : 60
% 0.13/0.32  % WCLimit    : 600
% 0.13/0.32  % DateTime   : Tue Dec  1 17:22:02 EST 2020
% 0.13/0.32  % CPUTime    : 
% 0.18/0.39  % (29888)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.18/0.49  % (29879)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.18/0.49  % (29880)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.18/0.49  % (29885)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.18/0.49  % (29885)Refutation not found, incomplete strategy% (29885)------------------------------
% 0.18/0.49  % (29885)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.49  % (29885)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.49  
% 0.18/0.49  % (29885)Memory used [KB]: 6140
% 0.18/0.49  % (29885)Time elapsed: 0.101 s
% 0.18/0.49  % (29885)------------------------------
% 0.18/0.49  % (29885)------------------------------
% 0.18/0.49  % (29886)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.18/0.49  % (29893)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.18/0.49  % (29884)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.18/0.49  % (29889)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.18/0.50  % (29875)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.18/0.50  % (29875)Refutation not found, incomplete strategy% (29875)------------------------------
% 0.18/0.50  % (29875)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.50  % (29875)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.50  
% 0.18/0.50  % (29875)Memory used [KB]: 6140
% 0.18/0.50  % (29875)Time elapsed: 0.102 s
% 0.18/0.50  % (29875)------------------------------
% 0.18/0.50  % (29875)------------------------------
% 0.18/0.50  % (29878)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.18/0.50  % (29883)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.18/0.50  % (29881)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.18/0.50  % (29882)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.18/0.50  % (29876)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.18/0.51  % (29895)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.18/0.51  % (29892)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.18/0.51  % (29895)Refutation not found, incomplete strategy% (29895)------------------------------
% 0.18/0.51  % (29895)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (29895)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.51  
% 0.18/0.51  % (29895)Memory used [KB]: 10618
% 0.18/0.51  % (29895)Time elapsed: 0.125 s
% 0.18/0.51  % (29895)------------------------------
% 0.18/0.51  % (29895)------------------------------
% 0.18/0.51  % (29876)Refutation not found, incomplete strategy% (29876)------------------------------
% 0.18/0.51  % (29876)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.51  % (29876)Termination reason: Refutation not found, incomplete strategy
% 0.18/0.51  
% 0.18/0.51  % (29876)Memory used [KB]: 10618
% 0.18/0.51  % (29876)Time elapsed: 0.106 s
% 0.18/0.51  % (29876)------------------------------
% 0.18/0.51  % (29876)------------------------------
% 0.18/0.51  % (29891)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.18/0.51  % (29877)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.18/0.51  % (29890)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.18/0.51  % (29894)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.18/0.52  % (29887)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 1.63/0.59  % (29891)Refutation found. Thanks to Tanya!
% 1.63/0.59  % SZS status Theorem for theBenchmark
% 1.63/0.59  % SZS output start Proof for theBenchmark
% 1.63/0.59  fof(f2521,plain,(
% 1.63/0.59    $false),
% 1.63/0.59    inference(avatar_sat_refutation,[],[f67,f72,f77,f82,f87,f92,f97,f102,f107,f112,f117,f122,f151,f188,f260,f285,f536,f541,f546,f719,f724,f729,f1362,f1378,f1390,f1929,f2361,f2507])).
% 1.63/0.59  fof(f2507,plain,(
% 1.63/0.59    ~spl5_14 | ~spl5_17 | ~spl5_98 | spl5_183 | ~spl5_259 | ~spl5_315),
% 1.63/0.59    inference(avatar_contradiction_clause,[],[f2506])).
% 1.63/0.59  fof(f2506,plain,(
% 1.63/0.59    $false | (~spl5_14 | ~spl5_17 | ~spl5_98 | spl5_183 | ~spl5_259 | ~spl5_315)),
% 1.63/0.59    inference(subsumption_resolution,[],[f2505,f1389])).
% 1.63/0.59  fof(f1389,plain,(
% 1.63/0.59    ~r1_tarski(k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)),u1_struct_0(sK3)) | spl5_183),
% 1.63/0.59    inference(avatar_component_clause,[],[f1387])).
% 1.63/0.59  fof(f1387,plain,(
% 1.63/0.59    spl5_183 <=> r1_tarski(k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)),u1_struct_0(sK3))),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_183])])).
% 1.63/0.59  fof(f2505,plain,(
% 1.63/0.59    r1_tarski(k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)),u1_struct_0(sK3)) | (~spl5_14 | ~spl5_17 | ~spl5_98 | ~spl5_259 | ~spl5_315)),
% 1.63/0.59    inference(forward_demodulation,[],[f2407,f1928])).
% 1.63/0.59  fof(f1928,plain,(
% 1.63/0.59    k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)) = u1_struct_0(k1_tsep_1(sK3,sK2,sK4)) | ~spl5_259),
% 1.63/0.59    inference(avatar_component_clause,[],[f1926])).
% 1.63/0.59  fof(f1926,plain,(
% 1.63/0.59    spl5_259 <=> k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)) = u1_struct_0(k1_tsep_1(sK3,sK2,sK4))),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_259])])).
% 1.63/0.59  fof(f2407,plain,(
% 1.63/0.59    r1_tarski(u1_struct_0(k1_tsep_1(sK3,sK2,sK4)),u1_struct_0(sK3)) | (~spl5_14 | ~spl5_17 | ~spl5_98 | ~spl5_315)),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f172,f139,f728,f728,f2360,f57])).
% 1.63/0.59  fof(f57,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f34])).
% 1.63/0.59  fof(f34,plain,(
% 1.63/0.59    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.63/0.59    inference(nnf_transformation,[],[f22])).
% 1.63/0.59  fof(f22,plain,(
% 1.63/0.59    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.63/0.59    inference(flattening,[],[f21])).
% 1.63/0.59  fof(f21,plain,(
% 1.63/0.59    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.63/0.59    inference(ennf_transformation,[],[f7])).
% 1.63/0.59  fof(f7,axiom,(
% 1.63/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 1.63/0.59  fof(f2360,plain,(
% 1.63/0.59    m1_pre_topc(sK3,sK3) | ~spl5_315),
% 1.63/0.59    inference(avatar_component_clause,[],[f2358])).
% 1.63/0.59  fof(f2358,plain,(
% 1.63/0.59    spl5_315 <=> m1_pre_topc(sK3,sK3)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_315])])).
% 1.63/0.59  fof(f728,plain,(
% 1.63/0.59    m1_pre_topc(k1_tsep_1(sK3,sK2,sK4),sK3) | ~spl5_98),
% 1.63/0.59    inference(avatar_component_clause,[],[f726])).
% 1.63/0.59  fof(f726,plain,(
% 1.63/0.59    spl5_98 <=> m1_pre_topc(k1_tsep_1(sK3,sK2,sK4),sK3)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).
% 1.63/0.59  fof(f139,plain,(
% 1.63/0.59    l1_pre_topc(sK3) | ~spl5_14),
% 1.63/0.59    inference(avatar_component_clause,[],[f137])).
% 1.63/0.59  fof(f137,plain,(
% 1.63/0.59    spl5_14 <=> l1_pre_topc(sK3)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.63/0.59  fof(f172,plain,(
% 1.63/0.59    v2_pre_topc(sK3) | ~spl5_17),
% 1.63/0.59    inference(avatar_component_clause,[],[f170])).
% 1.63/0.59  fof(f170,plain,(
% 1.63/0.59    spl5_17 <=> v2_pre_topc(sK3)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.63/0.59  fof(f2361,plain,(
% 1.63/0.59    spl5_315 | ~spl5_6 | spl5_7 | ~spl5_10 | ~spl5_11 | spl5_12),
% 1.63/0.59    inference(avatar_split_clause,[],[f2321,f119,f114,f109,f94,f89,f2358])).
% 1.63/0.59  fof(f89,plain,(
% 1.63/0.59    spl5_6 <=> m1_pre_topc(sK3,sK1)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.63/0.59  fof(f94,plain,(
% 1.63/0.59    spl5_7 <=> v2_struct_0(sK3)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.63/0.59  fof(f109,plain,(
% 1.63/0.59    spl5_10 <=> l1_pre_topc(sK1)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.63/0.59  fof(f114,plain,(
% 1.63/0.59    spl5_11 <=> v2_pre_topc(sK1)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.63/0.59  fof(f119,plain,(
% 1.63/0.59    spl5_12 <=> v2_struct_0(sK1)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.63/0.59  fof(f2321,plain,(
% 1.63/0.59    m1_pre_topc(sK3,sK3) | (~spl5_6 | spl5_7 | ~spl5_10 | ~spl5_11 | spl5_12)),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f121,f116,f111,f96,f91,f763])).
% 1.63/0.59  fof(f763,plain,(
% 1.63/0.59    ( ! [X0,X1] : (m1_pre_topc(X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.59    inference(trivial_inequality_removal,[],[f762])).
% 1.63/0.59  fof(f762,plain,(
% 1.63/0.59    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | m1_pre_topc(X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.59    inference(duplicate_literal_removal,[],[f755])).
% 1.63/0.59  fof(f755,plain,(
% 1.63/0.59    ( ! [X0,X1] : (g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) != g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | m1_pre_topc(X1,X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.59    inference(superposition,[],[f52,f50])).
% 1.63/0.59  fof(f50,plain,(
% 1.63/0.59    ( ! [X0,X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f14])).
% 1.63/0.59  fof(f14,plain,(
% 1.63/0.59    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(flattening,[],[f13])).
% 1.63/0.59  fof(f13,plain,(
% 1.63/0.59    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.63/0.59    inference(ennf_transformation,[],[f6])).
% 1.63/0.59  fof(f6,axiom,(
% 1.63/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).
% 1.63/0.59  fof(f52,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f32])).
% 1.63/0.59  fof(f32,plain,(
% 1.63/0.59    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X2) | k1_tsep_1(X0,X1,X2) != g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) & (k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2)) | ~m1_pre_topc(X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(nnf_transformation,[],[f16])).
% 1.63/0.59  fof(f16,plain,(
% 1.63/0.59    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(flattening,[],[f15])).
% 1.63/0.59  fof(f15,plain,(
% 1.63/0.59    ! [X0] : (! [X1] : (! [X2] : ((m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.63/0.59    inference(ennf_transformation,[],[f5])).
% 1.63/0.59  fof(f5,axiom,(
% 1.63/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (m1_pre_topc(X1,X2) <=> k1_tsep_1(X0,X1,X2) = g1_pre_topc(u1_struct_0(X2),u1_pre_topc(X2))))))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_tsep_1)).
% 1.63/0.59  fof(f91,plain,(
% 1.63/0.59    m1_pre_topc(sK3,sK1) | ~spl5_6),
% 1.63/0.59    inference(avatar_component_clause,[],[f89])).
% 1.63/0.59  fof(f96,plain,(
% 1.63/0.59    ~v2_struct_0(sK3) | spl5_7),
% 1.63/0.59    inference(avatar_component_clause,[],[f94])).
% 1.63/0.59  fof(f111,plain,(
% 1.63/0.59    l1_pre_topc(sK1) | ~spl5_10),
% 1.63/0.59    inference(avatar_component_clause,[],[f109])).
% 1.63/0.59  fof(f116,plain,(
% 1.63/0.59    v2_pre_topc(sK1) | ~spl5_11),
% 1.63/0.59    inference(avatar_component_clause,[],[f114])).
% 1.63/0.59  fof(f121,plain,(
% 1.63/0.59    ~v2_struct_0(sK1) | spl5_12),
% 1.63/0.59    inference(avatar_component_clause,[],[f119])).
% 1.63/0.59  fof(f1929,plain,(
% 1.63/0.59    spl5_259 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_7 | spl5_9 | ~spl5_14 | spl5_96 | ~spl5_97 | ~spl5_98),
% 1.63/0.59    inference(avatar_split_clause,[],[f1858,f726,f721,f716,f137,f104,f94,f84,f74,f69,f1926])).
% 1.63/0.59  fof(f69,plain,(
% 1.63/0.59    spl5_2 <=> m1_pre_topc(sK4,sK3)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.63/0.59  fof(f74,plain,(
% 1.63/0.59    spl5_3 <=> m1_pre_topc(sK2,sK3)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.63/0.59  fof(f84,plain,(
% 1.63/0.59    spl5_5 <=> v2_struct_0(sK4)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.63/0.59  fof(f104,plain,(
% 1.63/0.59    spl5_9 <=> v2_struct_0(sK2)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.63/0.59  fof(f716,plain,(
% 1.63/0.59    spl5_96 <=> v2_struct_0(k1_tsep_1(sK3,sK2,sK4))),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_96])])).
% 1.63/0.59  fof(f721,plain,(
% 1.63/0.59    spl5_97 <=> v1_pre_topc(k1_tsep_1(sK3,sK2,sK4))),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).
% 1.63/0.59  fof(f1858,plain,(
% 1.63/0.59    k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)) = u1_struct_0(k1_tsep_1(sK3,sK2,sK4)) | (~spl5_2 | ~spl5_3 | spl5_5 | spl5_7 | spl5_9 | ~spl5_14 | spl5_96 | ~spl5_97 | ~spl5_98)),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f96,f139,f106,f86,f76,f71,f718,f723,f728,f62])).
% 1.63/0.59  fof(f62,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.59    inference(equality_resolution,[],[f53])).
% 1.63/0.59  fof(f53,plain,(
% 1.63/0.59    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f33])).
% 1.63/0.59  fof(f33,plain,(
% 1.63/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k1_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(nnf_transformation,[],[f18])).
% 1.63/0.59  fof(f18,plain,(
% 1.63/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(flattening,[],[f17])).
% 1.63/0.59  fof(f17,plain,(
% 1.63/0.59    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.63/0.59    inference(ennf_transformation,[],[f3])).
% 1.63/0.59  fof(f3,axiom,(
% 1.63/0.59    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tsep_1)).
% 1.63/0.59  fof(f723,plain,(
% 1.63/0.59    v1_pre_topc(k1_tsep_1(sK3,sK2,sK4)) | ~spl5_97),
% 1.63/0.59    inference(avatar_component_clause,[],[f721])).
% 1.63/0.59  fof(f718,plain,(
% 1.63/0.59    ~v2_struct_0(k1_tsep_1(sK3,sK2,sK4)) | spl5_96),
% 1.63/0.59    inference(avatar_component_clause,[],[f716])).
% 1.63/0.59  fof(f71,plain,(
% 1.63/0.59    m1_pre_topc(sK4,sK3) | ~spl5_2),
% 1.63/0.59    inference(avatar_component_clause,[],[f69])).
% 1.63/0.59  fof(f76,plain,(
% 1.63/0.59    m1_pre_topc(sK2,sK3) | ~spl5_3),
% 1.63/0.59    inference(avatar_component_clause,[],[f74])).
% 1.63/0.59  fof(f86,plain,(
% 1.63/0.59    ~v2_struct_0(sK4) | spl5_5),
% 1.63/0.59    inference(avatar_component_clause,[],[f84])).
% 1.63/0.59  fof(f106,plain,(
% 1.63/0.59    ~v2_struct_0(sK2) | spl5_9),
% 1.63/0.59    inference(avatar_component_clause,[],[f104])).
% 1.63/0.59  fof(f1390,plain,(
% 1.63/0.59    ~spl5_183 | spl5_178 | ~spl5_181),
% 1.63/0.59    inference(avatar_split_clause,[],[f1385,f1375,f1359,f1387])).
% 1.63/0.59  fof(f1359,plain,(
% 1.63/0.59    spl5_178 <=> r1_tarski(u1_struct_0(k1_tsep_1(sK1,sK2,sK4)),u1_struct_0(sK3))),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_178])])).
% 1.63/0.59  fof(f1375,plain,(
% 1.63/0.59    spl5_181 <=> u1_struct_0(k1_tsep_1(sK1,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4))),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_181])])).
% 1.63/0.59  fof(f1385,plain,(
% 1.63/0.59    ~r1_tarski(k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)),u1_struct_0(sK3)) | (spl5_178 | ~spl5_181)),
% 1.63/0.59    inference(forward_demodulation,[],[f1361,f1377])).
% 1.63/0.59  fof(f1377,plain,(
% 1.63/0.59    u1_struct_0(k1_tsep_1(sK1,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)) | ~spl5_181),
% 1.63/0.59    inference(avatar_component_clause,[],[f1375])).
% 1.63/0.59  fof(f1361,plain,(
% 1.63/0.59    ~r1_tarski(u1_struct_0(k1_tsep_1(sK1,sK2,sK4)),u1_struct_0(sK3)) | spl5_178),
% 1.63/0.59    inference(avatar_component_clause,[],[f1359])).
% 1.63/0.59  fof(f1378,plain,(
% 1.63/0.59    spl5_181 | ~spl5_4 | spl5_5 | ~spl5_8 | spl5_9 | ~spl5_10 | spl5_12 | spl5_71 | ~spl5_72 | ~spl5_73),
% 1.63/0.59    inference(avatar_split_clause,[],[f1258,f543,f538,f533,f119,f109,f104,f99,f84,f79,f1375])).
% 1.63/0.59  fof(f79,plain,(
% 1.63/0.59    spl5_4 <=> m1_pre_topc(sK4,sK1)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.63/0.59  fof(f99,plain,(
% 1.63/0.59    spl5_8 <=> m1_pre_topc(sK2,sK1)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.63/0.59  fof(f533,plain,(
% 1.63/0.59    spl5_71 <=> v2_struct_0(k1_tsep_1(sK1,sK2,sK4))),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_71])])).
% 1.63/0.59  fof(f538,plain,(
% 1.63/0.59    spl5_72 <=> v1_pre_topc(k1_tsep_1(sK1,sK2,sK4))),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).
% 1.63/0.59  fof(f543,plain,(
% 1.63/0.59    spl5_73 <=> m1_pre_topc(k1_tsep_1(sK1,sK2,sK4),sK1)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_73])])).
% 1.63/0.59  fof(f1258,plain,(
% 1.63/0.59    u1_struct_0(k1_tsep_1(sK1,sK2,sK4)) = k2_xboole_0(u1_struct_0(sK2),u1_struct_0(sK4)) | (~spl5_4 | spl5_5 | ~spl5_8 | spl5_9 | ~spl5_10 | spl5_12 | spl5_71 | ~spl5_72 | ~spl5_73)),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f121,f111,f106,f86,f101,f81,f535,f540,f545,f62])).
% 1.63/0.59  fof(f545,plain,(
% 1.63/0.59    m1_pre_topc(k1_tsep_1(sK1,sK2,sK4),sK1) | ~spl5_73),
% 1.63/0.59    inference(avatar_component_clause,[],[f543])).
% 1.63/0.59  fof(f540,plain,(
% 1.63/0.59    v1_pre_topc(k1_tsep_1(sK1,sK2,sK4)) | ~spl5_72),
% 1.63/0.59    inference(avatar_component_clause,[],[f538])).
% 1.63/0.59  fof(f535,plain,(
% 1.63/0.59    ~v2_struct_0(k1_tsep_1(sK1,sK2,sK4)) | spl5_71),
% 1.63/0.59    inference(avatar_component_clause,[],[f533])).
% 1.63/0.59  fof(f81,plain,(
% 1.63/0.59    m1_pre_topc(sK4,sK1) | ~spl5_4),
% 1.63/0.59    inference(avatar_component_clause,[],[f79])).
% 1.63/0.59  fof(f101,plain,(
% 1.63/0.59    m1_pre_topc(sK2,sK1) | ~spl5_8),
% 1.63/0.59    inference(avatar_component_clause,[],[f99])).
% 1.63/0.59  fof(f1362,plain,(
% 1.63/0.59    ~spl5_178 | spl5_1 | ~spl5_6 | ~spl5_10 | ~spl5_11 | ~spl5_73),
% 1.63/0.59    inference(avatar_split_clause,[],[f1263,f543,f114,f109,f89,f64,f1359])).
% 1.63/0.59  fof(f64,plain,(
% 1.63/0.59    spl5_1 <=> m1_pre_topc(k1_tsep_1(sK1,sK2,sK4),sK3)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.63/0.59  fof(f1263,plain,(
% 1.63/0.59    ~r1_tarski(u1_struct_0(k1_tsep_1(sK1,sK2,sK4)),u1_struct_0(sK3)) | (spl5_1 | ~spl5_6 | ~spl5_10 | ~spl5_11 | ~spl5_73)),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f116,f111,f91,f66,f545,f56])).
% 1.63/0.59  fof(f56,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f34])).
% 1.63/0.59  fof(f66,plain,(
% 1.63/0.59    ~m1_pre_topc(k1_tsep_1(sK1,sK2,sK4),sK3) | spl5_1),
% 1.63/0.59    inference(avatar_component_clause,[],[f64])).
% 1.63/0.59  fof(f729,plain,(
% 1.63/0.59    spl5_98 | ~spl5_32),
% 1.63/0.59    inference(avatar_split_clause,[],[f712,f282,f726])).
% 1.63/0.59  fof(f282,plain,(
% 1.63/0.59    spl5_32 <=> sP0(sK3,sK4,sK2)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 1.63/0.59  fof(f712,plain,(
% 1.63/0.59    m1_pre_topc(k1_tsep_1(sK3,sK2,sK4),sK3) | ~spl5_32),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f284,f60])).
% 1.63/0.59  fof(f60,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (m1_pre_topc(k1_tsep_1(X0,X2,X1),X0) | ~sP0(X0,X1,X2)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f36])).
% 1.63/0.59  fof(f36,plain,(
% 1.63/0.59    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X2,X1),X0) & v1_pre_topc(k1_tsep_1(X0,X2,X1)) & ~v2_struct_0(k1_tsep_1(X0,X2,X1))) | ~sP0(X0,X1,X2))),
% 1.63/0.59    inference(rectify,[],[f35])).
% 1.63/0.59  fof(f35,plain,(
% 1.63/0.59    ! [X0,X2,X1] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP0(X0,X2,X1))),
% 1.63/0.59    inference(nnf_transformation,[],[f25])).
% 1.63/0.59  fof(f25,plain,(
% 1.63/0.59    ! [X0,X2,X1] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~sP0(X0,X2,X1))),
% 1.63/0.59    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 1.63/0.59  fof(f284,plain,(
% 1.63/0.59    sP0(sK3,sK4,sK2) | ~spl5_32),
% 1.63/0.59    inference(avatar_component_clause,[],[f282])).
% 1.63/0.59  fof(f724,plain,(
% 1.63/0.59    spl5_97 | ~spl5_32),
% 1.63/0.59    inference(avatar_split_clause,[],[f713,f282,f721])).
% 1.63/0.59  fof(f713,plain,(
% 1.63/0.59    v1_pre_topc(k1_tsep_1(sK3,sK2,sK4)) | ~spl5_32),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f284,f59])).
% 1.63/0.59  fof(f59,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (v1_pre_topc(k1_tsep_1(X0,X2,X1)) | ~sP0(X0,X1,X2)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f36])).
% 1.63/0.59  fof(f719,plain,(
% 1.63/0.59    ~spl5_96 | ~spl5_32),
% 1.63/0.59    inference(avatar_split_clause,[],[f714,f282,f716])).
% 1.63/0.59  fof(f714,plain,(
% 1.63/0.59    ~v2_struct_0(k1_tsep_1(sK3,sK2,sK4)) | ~spl5_32),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f284,f58])).
% 1.63/0.59  fof(f58,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X2,X1)) | ~sP0(X0,X1,X2)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f36])).
% 1.63/0.59  fof(f546,plain,(
% 1.63/0.59    spl5_73 | ~spl5_27),
% 1.63/0.59    inference(avatar_split_clause,[],[f529,f257,f543])).
% 1.63/0.59  fof(f257,plain,(
% 1.63/0.59    spl5_27 <=> sP0(sK1,sK4,sK2)),
% 1.63/0.59    introduced(avatar_definition,[new_symbols(naming,[spl5_27])])).
% 1.63/0.59  fof(f529,plain,(
% 1.63/0.59    m1_pre_topc(k1_tsep_1(sK1,sK2,sK4),sK1) | ~spl5_27),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f259,f60])).
% 1.63/0.59  fof(f259,plain,(
% 1.63/0.59    sP0(sK1,sK4,sK2) | ~spl5_27),
% 1.63/0.59    inference(avatar_component_clause,[],[f257])).
% 1.63/0.59  fof(f541,plain,(
% 1.63/0.59    spl5_72 | ~spl5_27),
% 1.63/0.59    inference(avatar_split_clause,[],[f530,f257,f538])).
% 1.63/0.59  fof(f530,plain,(
% 1.63/0.59    v1_pre_topc(k1_tsep_1(sK1,sK2,sK4)) | ~spl5_27),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f259,f59])).
% 1.63/0.59  fof(f536,plain,(
% 1.63/0.59    ~spl5_71 | ~spl5_27),
% 1.63/0.59    inference(avatar_split_clause,[],[f531,f257,f533])).
% 1.63/0.59  fof(f531,plain,(
% 1.63/0.59    ~v2_struct_0(k1_tsep_1(sK1,sK2,sK4)) | ~spl5_27),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f259,f58])).
% 1.63/0.59  fof(f285,plain,(
% 1.63/0.59    spl5_32 | ~spl5_2 | ~spl5_3 | spl5_5 | spl5_7 | spl5_9 | ~spl5_14),
% 1.63/0.59    inference(avatar_split_clause,[],[f214,f137,f104,f94,f84,f74,f69,f282])).
% 1.63/0.59  fof(f214,plain,(
% 1.63/0.59    sP0(sK3,sK4,sK2) | (~spl5_2 | ~spl5_3 | spl5_5 | spl5_7 | spl5_9 | ~spl5_14)),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f96,f139,f106,f76,f86,f71,f61])).
% 1.63/0.59  fof(f61,plain,(
% 1.63/0.59    ( ! [X2,X0,X1] : (sP0(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f26])).
% 1.63/0.59  fof(f26,plain,(
% 1.63/0.59    ! [X0,X1,X2] : (sP0(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(definition_folding,[],[f24,f25])).
% 1.63/0.59  fof(f24,plain,(
% 1.63/0.59    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.63/0.59    inference(flattening,[],[f23])).
% 1.63/0.59  fof(f23,plain,(
% 1.63/0.59    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.63/0.59    inference(ennf_transformation,[],[f4])).
% 1.63/0.59  fof(f4,axiom,(
% 1.63/0.59    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 1.63/0.59  fof(f260,plain,(
% 1.63/0.59    spl5_27 | ~spl5_4 | spl5_5 | ~spl5_8 | spl5_9 | ~spl5_10 | spl5_12),
% 1.63/0.59    inference(avatar_split_clause,[],[f219,f119,f109,f104,f99,f84,f79,f257])).
% 1.63/0.59  fof(f219,plain,(
% 1.63/0.59    sP0(sK1,sK4,sK2) | (~spl5_4 | spl5_5 | ~spl5_8 | spl5_9 | ~spl5_10 | spl5_12)),
% 1.63/0.59    inference(unit_resulting_resolution,[],[f121,f111,f106,f101,f86,f81,f61])).
% 1.63/0.59  fof(f188,plain,(
% 1.63/0.59    spl5_17 | ~spl5_6 | ~spl5_10 | ~spl5_11),
% 1.63/0.59    inference(avatar_split_clause,[],[f187,f114,f109,f89,f170])).
% 1.63/0.59  fof(f187,plain,(
% 1.63/0.59    v2_pre_topc(sK3) | (~spl5_6 | ~spl5_10 | ~spl5_11)),
% 1.63/0.59    inference(subsumption_resolution,[],[f186,f116])).
% 1.63/0.59  fof(f186,plain,(
% 1.63/0.59    v2_pre_topc(sK3) | ~v2_pre_topc(sK1) | (~spl5_6 | ~spl5_10)),
% 1.63/0.59    inference(subsumption_resolution,[],[f162,f111])).
% 1.63/0.59  fof(f162,plain,(
% 1.63/0.59    v2_pre_topc(sK3) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~spl5_6),
% 1.63/0.59    inference(resolution,[],[f55,f91])).
% 1.63/0.59  fof(f55,plain,(
% 1.63/0.59    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f20])).
% 1.63/0.59  fof(f20,plain,(
% 1.63/0.59    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.63/0.59    inference(flattening,[],[f19])).
% 1.63/0.59  fof(f19,plain,(
% 1.63/0.59    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.63/0.59    inference(ennf_transformation,[],[f1])).
% 1.63/0.59  fof(f1,axiom,(
% 1.63/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 1.63/0.59  fof(f151,plain,(
% 1.63/0.59    spl5_14 | ~spl5_6 | ~spl5_10),
% 1.63/0.59    inference(avatar_split_clause,[],[f150,f109,f89,f137])).
% 1.63/0.59  fof(f150,plain,(
% 1.63/0.59    l1_pre_topc(sK3) | (~spl5_6 | ~spl5_10)),
% 1.63/0.59    inference(subsumption_resolution,[],[f129,f111])).
% 1.63/0.59  fof(f129,plain,(
% 1.63/0.59    l1_pre_topc(sK3) | ~l1_pre_topc(sK1) | ~spl5_6),
% 1.63/0.59    inference(resolution,[],[f49,f91])).
% 1.63/0.59  fof(f49,plain,(
% 1.63/0.59    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 1.63/0.59    inference(cnf_transformation,[],[f12])).
% 1.63/0.59  fof(f12,plain,(
% 1.63/0.59    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.63/0.59    inference(ennf_transformation,[],[f2])).
% 1.63/0.59  fof(f2,axiom,(
% 1.63/0.59    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.63/0.59  fof(f122,plain,(
% 1.63/0.59    ~spl5_12),
% 1.63/0.59    inference(avatar_split_clause,[],[f37,f119])).
% 1.63/0.59  fof(f37,plain,(
% 1.63/0.59    ~v2_struct_0(sK1)),
% 1.63/0.59    inference(cnf_transformation,[],[f31])).
% 1.63/0.59  fof(f31,plain,(
% 1.63/0.59    (((~m1_pre_topc(k1_tsep_1(sK1,sK2,sK4),sK3) & m1_pre_topc(sK4,sK3) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 1.63/0.59    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f11,f30,f29,f28,f27])).
% 1.63/0.59  fof(f27,plain,(
% 1.63/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK1,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 1.63/0.59    introduced(choice_axiom,[])).
% 1.63/0.59  fof(f28,plain,(
% 1.63/0.59    ? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK1,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK1,sK2,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK2,X2) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2))),
% 1.63/0.59    introduced(choice_axiom,[])).
% 1.63/0.59  fof(f29,plain,(
% 1.63/0.59    ? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(sK1,sK2,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(sK2,X2) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k1_tsep_1(sK1,sK2,X3),sK3) & m1_pre_topc(X3,sK3) & m1_pre_topc(sK2,sK3) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3))),
% 1.63/0.59    introduced(choice_axiom,[])).
% 1.63/0.59  fof(f30,plain,(
% 1.63/0.59    ? [X3] : (~m1_pre_topc(k1_tsep_1(sK1,sK2,X3),sK3) & m1_pre_topc(X3,sK3) & m1_pre_topc(sK2,sK3) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) => (~m1_pre_topc(k1_tsep_1(sK1,sK2,sK4),sK3) & m1_pre_topc(sK4,sK3) & m1_pre_topc(sK2,sK3) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4))),
% 1.63/0.59    introduced(choice_axiom,[])).
% 1.63/0.59  fof(f11,plain,(
% 1.63/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.63/0.59    inference(flattening,[],[f10])).
% 1.63/0.59  fof(f10,plain,(
% 1.63/0.59    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((~m1_pre_topc(k1_tsep_1(X0,X1,X3),X2) & (m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.63/0.59    inference(ennf_transformation,[],[f9])).
% 1.63/0.59  fof(f9,negated_conjecture,(
% 1.63/0.59    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 1.63/0.59    inference(negated_conjecture,[],[f8])).
% 1.63/0.59  fof(f8,conjecture,(
% 1.63/0.59    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X3,X2) & m1_pre_topc(X1,X2)) => m1_pre_topc(k1_tsep_1(X0,X1,X3),X2))))))),
% 1.63/0.59    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tmap_1)).
% 1.63/0.59  fof(f117,plain,(
% 1.63/0.59    spl5_11),
% 1.63/0.59    inference(avatar_split_clause,[],[f38,f114])).
% 1.63/0.59  fof(f38,plain,(
% 1.63/0.59    v2_pre_topc(sK1)),
% 1.63/0.59    inference(cnf_transformation,[],[f31])).
% 1.63/0.59  fof(f112,plain,(
% 1.63/0.59    spl5_10),
% 1.63/0.59    inference(avatar_split_clause,[],[f39,f109])).
% 1.63/0.59  fof(f39,plain,(
% 1.63/0.59    l1_pre_topc(sK1)),
% 1.63/0.59    inference(cnf_transformation,[],[f31])).
% 1.63/0.59  fof(f107,plain,(
% 1.63/0.59    ~spl5_9),
% 1.63/0.59    inference(avatar_split_clause,[],[f40,f104])).
% 1.63/0.59  fof(f40,plain,(
% 1.63/0.59    ~v2_struct_0(sK2)),
% 1.63/0.59    inference(cnf_transformation,[],[f31])).
% 1.63/0.59  fof(f102,plain,(
% 1.63/0.59    spl5_8),
% 1.63/0.59    inference(avatar_split_clause,[],[f41,f99])).
% 1.63/0.59  fof(f41,plain,(
% 1.63/0.59    m1_pre_topc(sK2,sK1)),
% 1.63/0.59    inference(cnf_transformation,[],[f31])).
% 1.63/0.59  fof(f97,plain,(
% 1.63/0.59    ~spl5_7),
% 1.63/0.59    inference(avatar_split_clause,[],[f42,f94])).
% 1.63/0.59  fof(f42,plain,(
% 1.63/0.59    ~v2_struct_0(sK3)),
% 1.63/0.59    inference(cnf_transformation,[],[f31])).
% 1.63/0.59  fof(f92,plain,(
% 1.63/0.59    spl5_6),
% 1.63/0.59    inference(avatar_split_clause,[],[f43,f89])).
% 1.63/0.59  fof(f43,plain,(
% 1.63/0.59    m1_pre_topc(sK3,sK1)),
% 1.63/0.59    inference(cnf_transformation,[],[f31])).
% 1.63/0.59  fof(f87,plain,(
% 1.63/0.59    ~spl5_5),
% 1.63/0.59    inference(avatar_split_clause,[],[f44,f84])).
% 1.63/0.59  fof(f44,plain,(
% 1.63/0.59    ~v2_struct_0(sK4)),
% 1.63/0.59    inference(cnf_transformation,[],[f31])).
% 1.63/0.59  fof(f82,plain,(
% 1.63/0.59    spl5_4),
% 1.63/0.59    inference(avatar_split_clause,[],[f45,f79])).
% 1.63/0.59  fof(f45,plain,(
% 1.63/0.59    m1_pre_topc(sK4,sK1)),
% 1.63/0.59    inference(cnf_transformation,[],[f31])).
% 1.63/0.59  fof(f77,plain,(
% 1.63/0.59    spl5_3),
% 1.63/0.59    inference(avatar_split_clause,[],[f46,f74])).
% 1.63/0.59  fof(f46,plain,(
% 1.63/0.59    m1_pre_topc(sK2,sK3)),
% 1.63/0.59    inference(cnf_transformation,[],[f31])).
% 1.63/0.59  fof(f72,plain,(
% 1.63/0.59    spl5_2),
% 1.63/0.59    inference(avatar_split_clause,[],[f47,f69])).
% 1.63/0.59  fof(f47,plain,(
% 1.63/0.59    m1_pre_topc(sK4,sK3)),
% 1.63/0.59    inference(cnf_transformation,[],[f31])).
% 1.63/0.59  fof(f67,plain,(
% 1.63/0.59    ~spl5_1),
% 1.63/0.59    inference(avatar_split_clause,[],[f48,f64])).
% 1.63/0.59  fof(f48,plain,(
% 1.63/0.59    ~m1_pre_topc(k1_tsep_1(sK1,sK2,sK4),sK3)),
% 1.63/0.59    inference(cnf_transformation,[],[f31])).
% 1.63/0.59  % SZS output end Proof for theBenchmark
% 1.63/0.59  % (29891)------------------------------
% 1.63/0.59  % (29891)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.63/0.59  % (29891)Termination reason: Refutation
% 1.63/0.59  
% 1.63/0.59  % (29891)Memory used [KB]: 12665
% 1.63/0.59  % (29891)Time elapsed: 0.211 s
% 1.63/0.59  % (29891)------------------------------
% 1.63/0.59  % (29891)------------------------------
% 1.63/0.59  % (29874)Success in time 0.255 s
%------------------------------------------------------------------------------
