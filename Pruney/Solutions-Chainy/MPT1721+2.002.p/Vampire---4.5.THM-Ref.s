%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:05 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  176 ( 494 expanded)
%              Number of leaves         :   43 ( 245 expanded)
%              Depth                    :    9
%              Number of atoms          :  746 (2981 expanded)
%              Number of equality atoms :   23 (  39 expanded)
%              Maximal formula depth    :   17 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3985,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f89,f94,f99,f104,f109,f114,f119,f124,f129,f156,f192,f259,f299,f458,f463,f468,f630,f774,f779,f784,f1333,f1409,f1421,f2940,f3839,f3983])).

fof(f3983,plain,
    ( ~ spl5_16
    | ~ spl5_19
    | ~ spl5_112
    | spl5_207
    | ~ spl5_448
    | ~ spl5_583 ),
    inference(avatar_contradiction_clause,[],[f3982])).

fof(f3982,plain,
    ( $false
    | ~ spl5_16
    | ~ spl5_19
    | ~ spl5_112
    | spl5_207
    | ~ spl5_448
    | ~ spl5_583 ),
    inference(subsumption_resolution,[],[f3981,f1420])).

fof(f1420,plain,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)),u1_struct_0(sK4))
    | spl5_207 ),
    inference(avatar_component_clause,[],[f1418])).

fof(f1418,plain,
    ( spl5_207
  <=> r1_tarski(k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_207])])).

fof(f3981,plain,
    ( r1_tarski(k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)),u1_struct_0(sK4))
    | ~ spl5_16
    | ~ spl5_19
    | ~ spl5_112
    | ~ spl5_448
    | ~ spl5_583 ),
    inference(forward_demodulation,[],[f3872,f2939])).

fof(f2939,plain,
    ( k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK4,sK2,sK3))
    | ~ spl5_448 ),
    inference(avatar_component_clause,[],[f2937])).

fof(f2937,plain,
    ( spl5_448
  <=> k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK4,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_448])])).

fof(f3872,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK4,sK2,sK3)),u1_struct_0(sK4))
    | ~ spl5_16
    | ~ spl5_19
    | ~ spl5_112
    | ~ spl5_583 ),
    inference(unit_resulting_resolution,[],[f184,f151,f783,f783,f3838,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
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
    inference(nnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f3838,plain,
    ( m1_pre_topc(sK4,sK4)
    | ~ spl5_583 ),
    inference(avatar_component_clause,[],[f3836])).

fof(f3836,plain,
    ( spl5_583
  <=> m1_pre_topc(sK4,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_583])])).

fof(f783,plain,
    ( m1_pre_topc(k2_tsep_1(sK4,sK2,sK3),sK4)
    | ~ spl5_112 ),
    inference(avatar_component_clause,[],[f781])).

fof(f781,plain,
    ( spl5_112
  <=> m1_pre_topc(k2_tsep_1(sK4,sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).

fof(f151,plain,
    ( l1_pre_topc(sK4)
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f149])).

fof(f149,plain,
    ( spl5_16
  <=> l1_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f184,plain,
    ( v2_pre_topc(sK4)
    | ~ spl5_19 ),
    inference(avatar_component_clause,[],[f182])).

fof(f182,plain,
    ( spl5_19
  <=> v2_pre_topc(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).

fof(f3839,plain,
    ( spl5_583
    | ~ spl5_5
    | spl5_6
    | ~ spl5_11
    | ~ spl5_12
    | spl5_13
    | ~ spl5_87 ),
    inference(avatar_split_clause,[],[f3825,f627,f126,f121,f116,f91,f86,f3836])).

fof(f86,plain,
    ( spl5_5
  <=> m1_pre_topc(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f91,plain,
    ( spl5_6
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f116,plain,
    ( spl5_11
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f121,plain,
    ( spl5_12
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f126,plain,
    ( spl5_13
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f627,plain,
    ( spl5_87
  <=> m1_pre_topc(sK4,k1_tsep_1(sK1,sK4,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f3825,plain,
    ( m1_pre_topc(sK4,sK4)
    | ~ spl5_5
    | spl5_6
    | ~ spl5_11
    | ~ spl5_12
    | spl5_13
    | ~ spl5_87 ),
    inference(unit_resulting_resolution,[],[f128,f123,f118,f93,f88,f629,f339])).

fof(f339,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,k1_tsep_1(X1,X0,X0))
      | m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(subsumption_resolution,[],[f311,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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

fof(f311,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X2,k1_tsep_1(X1,X0,X0))
      | m1_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X0,X1)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X1)
      | ~ v2_pre_topc(X1)
      | v2_struct_0(X1) ) ),
    inference(superposition,[],[f52,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
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
         => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
      | m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_pre_topc(X1,X0)
          | ~ m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))
         => m1_pre_topc(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).

fof(f629,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK1,sK4,sK4))
    | ~ spl5_87 ),
    inference(avatar_component_clause,[],[f627])).

fof(f88,plain,
    ( m1_pre_topc(sK4,sK1)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f86])).

fof(f93,plain,
    ( ~ v2_struct_0(sK4)
    | spl5_6 ),
    inference(avatar_component_clause,[],[f91])).

fof(f118,plain,
    ( l1_pre_topc(sK1)
    | ~ spl5_11 ),
    inference(avatar_component_clause,[],[f116])).

fof(f123,plain,
    ( v2_pre_topc(sK1)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f121])).

fof(f128,plain,
    ( ~ v2_struct_0(sK1)
    | spl5_13 ),
    inference(avatar_component_clause,[],[f126])).

fof(f2940,plain,
    ( spl5_448
    | spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6
    | spl5_8
    | spl5_10
    | ~ spl5_16
    | spl5_110
    | ~ spl5_111
    | ~ spl5_112 ),
    inference(avatar_split_clause,[],[f2813,f781,f776,f771,f149,f111,f101,f91,f81,f76,f71,f2937])).

fof(f71,plain,
    ( spl5_2
  <=> r1_tsep_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f76,plain,
    ( spl5_3
  <=> m1_pre_topc(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f81,plain,
    ( spl5_4
  <=> m1_pre_topc(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f101,plain,
    ( spl5_8
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f111,plain,
    ( spl5_10
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f771,plain,
    ( spl5_110
  <=> v2_struct_0(k2_tsep_1(sK4,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).

fof(f776,plain,
    ( spl5_111
  <=> v1_pre_topc(k2_tsep_1(sK4,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).

fof(f2813,plain,
    ( k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK4,sK2,sK3))
    | spl5_2
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6
    | spl5_8
    | spl5_10
    | ~ spl5_16
    | spl5_110
    | ~ spl5_111
    | ~ spl5_112 ),
    inference(unit_resulting_resolution,[],[f93,f151,f113,f103,f83,f78,f73,f773,f778,f783,f64])).

fof(f64,plain,(
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
    inference(equality_resolution,[],[f55])).

fof(f55,plain,(
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
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(nnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
             => ( ~ r1_tsep_1(X1,X2)
               => ! [X3] :
                    ( ( m1_pre_topc(X3,X0)
                      & v1_pre_topc(X3)
                      & ~ v2_struct_0(X3) )
                   => ( k2_tsep_1(X0,X1,X2) = X3
                    <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).

fof(f778,plain,
    ( v1_pre_topc(k2_tsep_1(sK4,sK2,sK3))
    | ~ spl5_111 ),
    inference(avatar_component_clause,[],[f776])).

fof(f773,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK4,sK2,sK3))
    | spl5_110 ),
    inference(avatar_component_clause,[],[f771])).

fof(f73,plain,
    ( ~ r1_tsep_1(sK2,sK3)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f71])).

fof(f78,plain,
    ( m1_pre_topc(sK3,sK4)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f83,plain,
    ( m1_pre_topc(sK2,sK4)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f103,plain,
    ( ~ v2_struct_0(sK3)
    | spl5_8 ),
    inference(avatar_component_clause,[],[f101])).

fof(f113,plain,
    ( ~ v2_struct_0(sK2)
    | spl5_10 ),
    inference(avatar_component_clause,[],[f111])).

fof(f1421,plain,
    ( ~ spl5_207
    | spl5_190
    | ~ spl5_205 ),
    inference(avatar_split_clause,[],[f1416,f1406,f1330,f1418])).

fof(f1330,plain,
    ( spl5_190
  <=> r1_tarski(u1_struct_0(k2_tsep_1(sK1,sK2,sK3)),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_190])])).

fof(f1406,plain,
    ( spl5_205
  <=> u1_struct_0(k2_tsep_1(sK1,sK2,sK3)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_205])])).

fof(f1416,plain,
    ( ~ r1_tarski(k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)),u1_struct_0(sK4))
    | spl5_190
    | ~ spl5_205 ),
    inference(forward_demodulation,[],[f1332,f1408])).

fof(f1408,plain,
    ( u1_struct_0(k2_tsep_1(sK1,sK2,sK3)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | ~ spl5_205 ),
    inference(avatar_component_clause,[],[f1406])).

fof(f1332,plain,
    ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK1,sK2,sK3)),u1_struct_0(sK4))
    | spl5_190 ),
    inference(avatar_component_clause,[],[f1330])).

fof(f1409,plain,
    ( spl5_205
    | spl5_2
    | ~ spl5_7
    | spl5_8
    | ~ spl5_9
    | spl5_10
    | ~ spl5_11
    | spl5_13
    | spl5_59
    | ~ spl5_60
    | ~ spl5_61 ),
    inference(avatar_split_clause,[],[f1228,f465,f460,f455,f126,f116,f111,f106,f101,f96,f71,f1406])).

fof(f96,plain,
    ( spl5_7
  <=> m1_pre_topc(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f106,plain,
    ( spl5_9
  <=> m1_pre_topc(sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f455,plain,
    ( spl5_59
  <=> v2_struct_0(k2_tsep_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).

fof(f460,plain,
    ( spl5_60
  <=> v1_pre_topc(k2_tsep_1(sK1,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f465,plain,
    ( spl5_61
  <=> m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f1228,plain,
    ( u1_struct_0(k2_tsep_1(sK1,sK2,sK3)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))
    | spl5_2
    | ~ spl5_7
    | spl5_8
    | ~ spl5_9
    | spl5_10
    | ~ spl5_11
    | spl5_13
    | spl5_59
    | ~ spl5_60
    | ~ spl5_61 ),
    inference(unit_resulting_resolution,[],[f128,f118,f113,f103,f108,f98,f73,f457,f462,f467,f64])).

fof(f467,plain,
    ( m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK1)
    | ~ spl5_61 ),
    inference(avatar_component_clause,[],[f465])).

fof(f462,plain,
    ( v1_pre_topc(k2_tsep_1(sK1,sK2,sK3))
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f460])).

fof(f457,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | spl5_59 ),
    inference(avatar_component_clause,[],[f455])).

fof(f98,plain,
    ( m1_pre_topc(sK3,sK1)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f108,plain,
    ( m1_pre_topc(sK2,sK1)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f106])).

fof(f1333,plain,
    ( ~ spl5_190
    | spl5_1
    | ~ spl5_5
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_61 ),
    inference(avatar_split_clause,[],[f1246,f465,f121,f116,f86,f66,f1330])).

fof(f66,plain,
    ( spl5_1
  <=> m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1246,plain,
    ( ~ r1_tarski(u1_struct_0(k2_tsep_1(sK1,sK2,sK3)),u1_struct_0(sK4))
    | spl5_1
    | ~ spl5_5
    | ~ spl5_11
    | ~ spl5_12
    | ~ spl5_61 ),
    inference(unit_resulting_resolution,[],[f123,f118,f88,f68,f467,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f68,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK4)
    | spl5_1 ),
    inference(avatar_component_clause,[],[f66])).

fof(f784,plain,
    ( spl5_112
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f767,f296,f781])).

fof(f296,plain,
    ( spl5_34
  <=> sP0(sK4,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f767,plain,
    ( m1_pre_topc(k2_tsep_1(sK4,sK2,sK3),sK4)
    | ~ spl5_34 ),
    inference(unit_resulting_resolution,[],[f298,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X0)
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X2,X1),X0)
        & v1_pre_topc(k2_tsep_1(X0,X2,X1))
        & ~ v2_struct_0(k2_tsep_1(X0,X2,X1)) )
      | ~ sP0(X0,X1,X2) ) ),
    inference(rectify,[],[f36])).

fof(f36,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ sP0(X0,X2,X1) ) ),
    inference(nnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X2,X1] :
      ( ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
        & v1_pre_topc(k2_tsep_1(X0,X1,X2))
        & ~ v2_struct_0(k2_tsep_1(X0,X1,X2)) )
      | ~ sP0(X0,X2,X1) ) ),
    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).

fof(f298,plain,
    ( sP0(sK4,sK3,sK2)
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f296])).

fof(f779,plain,
    ( spl5_111
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f768,f296,f776])).

fof(f768,plain,
    ( v1_pre_topc(k2_tsep_1(sK4,sK2,sK3))
    | ~ spl5_34 ),
    inference(unit_resulting_resolution,[],[f298,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X2,X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f774,plain,
    ( ~ spl5_110
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f769,f296,f771])).

fof(f769,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK4,sK2,sK3))
    | ~ spl5_34 ),
    inference(unit_resulting_resolution,[],[f298,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X2,X1))
      | ~ sP0(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f630,plain,
    ( spl5_87
    | ~ spl5_5
    | spl5_6
    | ~ spl5_11
    | ~ spl5_12
    | spl5_13 ),
    inference(avatar_split_clause,[],[f573,f126,f121,f116,f91,f86,f627])).

fof(f573,plain,
    ( m1_pre_topc(sK4,k1_tsep_1(sK1,sK4,sK4))
    | ~ spl5_5
    | spl5_6
    | ~ spl5_11
    | ~ spl5_12
    | spl5_13 ),
    inference(unit_resulting_resolution,[],[f128,f123,f118,f93,f88,f93,f88,f54])).

fof(f54,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tsep_1)).

fof(f468,plain,
    ( spl5_61
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f451,f256,f465])).

fof(f256,plain,
    ( spl5_26
  <=> sP0(sK1,sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f451,plain,
    ( m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK1)
    | ~ spl5_26 ),
    inference(unit_resulting_resolution,[],[f258,f62])).

fof(f258,plain,
    ( sP0(sK1,sK3,sK2)
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f256])).

fof(f463,plain,
    ( spl5_60
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f452,f256,f460])).

fof(f452,plain,
    ( v1_pre_topc(k2_tsep_1(sK1,sK2,sK3))
    | ~ spl5_26 ),
    inference(unit_resulting_resolution,[],[f258,f61])).

fof(f458,plain,
    ( ~ spl5_59
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f453,f256,f455])).

fof(f453,plain,
    ( ~ v2_struct_0(k2_tsep_1(sK1,sK2,sK3))
    | ~ spl5_26 ),
    inference(unit_resulting_resolution,[],[f258,f60])).

fof(f299,plain,
    ( spl5_34
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6
    | spl5_8
    | spl5_10
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f228,f149,f111,f101,f91,f81,f76,f296])).

fof(f228,plain,
    ( sP0(sK4,sK3,sK2)
    | ~ spl5_3
    | ~ spl5_4
    | spl5_6
    | spl5_8
    | spl5_10
    | ~ spl5_16 ),
    inference(unit_resulting_resolution,[],[f93,f151,f113,f83,f103,f78,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( sP0(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( sP0(X0,X2,X1)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(definition_folding,[],[f26,f27])).

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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).

fof(f259,plain,
    ( spl5_26
    | ~ spl5_7
    | spl5_8
    | ~ spl5_9
    | spl5_10
    | ~ spl5_11
    | spl5_13 ),
    inference(avatar_split_clause,[],[f236,f126,f116,f111,f106,f101,f96,f256])).

fof(f236,plain,
    ( sP0(sK1,sK3,sK2)
    | ~ spl5_7
    | spl5_8
    | ~ spl5_9
    | spl5_10
    | ~ spl5_11
    | spl5_13 ),
    inference(unit_resulting_resolution,[],[f128,f118,f113,f108,f103,f98,f63])).

fof(f192,plain,
    ( spl5_19
    | ~ spl5_5
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(avatar_split_clause,[],[f191,f121,f116,f86,f182])).

fof(f191,plain,
    ( v2_pre_topc(sK4)
    | ~ spl5_5
    | ~ spl5_11
    | ~ spl5_12 ),
    inference(subsumption_resolution,[],[f190,f123])).

fof(f190,plain,
    ( v2_pre_topc(sK4)
    | ~ v2_pre_topc(sK1)
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f168,f118])).

fof(f168,plain,
    ( v2_pre_topc(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ spl5_5 ),
    inference(resolution,[],[f57,f88])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | v2_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
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

fof(f156,plain,
    ( spl5_16
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(avatar_split_clause,[],[f155,f116,f86,f149])).

fof(f155,plain,
    ( l1_pre_topc(sK4)
    | ~ spl5_5
    | ~ spl5_11 ),
    inference(subsumption_resolution,[],[f135,f118])).

fof(f135,plain,
    ( l1_pre_topc(sK4)
    | ~ l1_pre_topc(sK1)
    | ~ spl5_5 ),
    inference(resolution,[],[f51,f88])).

fof(f129,plain,(
    ~ spl5_13 ),
    inference(avatar_split_clause,[],[f38,f126])).

fof(f38,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK4)
    & ~ r1_tsep_1(sK2,sK3)
    & m1_pre_topc(sK3,sK4)
    & m1_pre_topc(sK2,sK4)
    & m1_pre_topc(sK4,sK1)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK1)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK1)
    & ~ v2_struct_0(sK2)
    & l1_pre_topc(sK1)
    & v2_pre_topc(sK1)
    & ~ v2_struct_0(sK1) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f12,f32,f31,f30,f29])).

fof(f29,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                    & ~ r1_tsep_1(X1,X2)
                    & m1_pre_topc(X2,X3)
                    & m1_pre_topc(X1,X3)
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
                  ( ~ m1_pre_topc(k2_tsep_1(sK1,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
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

fof(f30,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ~ m1_pre_topc(k2_tsep_1(sK1,X1,X2),X3)
                & ~ r1_tsep_1(X1,X2)
                & m1_pre_topc(X2,X3)
                & m1_pre_topc(X1,X3)
                & m1_pre_topc(X3,sK1)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK1)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,X2),X3)
              & ~ r1_tsep_1(sK2,X2)
              & m1_pre_topc(X2,X3)
              & m1_pre_topc(sK2,X3)
              & m1_pre_topc(X3,sK1)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK1)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK2,sK1)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f31,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,X2),X3)
            & ~ r1_tsep_1(sK2,X2)
            & m1_pre_topc(X2,X3)
            & m1_pre_topc(sK2,X3)
            & m1_pre_topc(X3,sK1)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK1)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),X3)
          & ~ r1_tsep_1(sK2,sK3)
          & m1_pre_topc(sK3,X3)
          & m1_pre_topc(sK2,X3)
          & m1_pre_topc(X3,sK1)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK3,sK1)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X3] :
        ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),X3)
        & ~ r1_tsep_1(sK2,sK3)
        & m1_pre_topc(sK3,X3)
        & m1_pre_topc(sK2,X3)
        & m1_pre_topc(X3,sK1)
        & ~ v2_struct_0(X3) )
   => ( ~ m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK4)
      & ~ r1_tsep_1(sK2,sK3)
      & m1_pre_topc(sK3,sK4)
      & m1_pre_topc(sK2,sK4)
      & m1_pre_topc(sK4,sK1)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
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
                  ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                  & ~ r1_tsep_1(X1,X2)
                  & m1_pre_topc(X2,X3)
                  & m1_pre_topc(X1,X3)
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
                   => ( ( m1_pre_topc(X2,X3)
                        & m1_pre_topc(X1,X3) )
                     => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                        | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
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
                 => ( ( m1_pre_topc(X2,X3)
                      & m1_pre_topc(X1,X3) )
                   => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X3)
                      | r1_tsep_1(X1,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tmap_1)).

fof(f124,plain,(
    spl5_12 ),
    inference(avatar_split_clause,[],[f39,f121])).

fof(f39,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f119,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f40,f116])).

fof(f40,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f114,plain,(
    ~ spl5_10 ),
    inference(avatar_split_clause,[],[f41,f111])).

fof(f41,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f33])).

fof(f109,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f42,f106])).

fof(f42,plain,(
    m1_pre_topc(sK2,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f104,plain,(
    ~ spl5_8 ),
    inference(avatar_split_clause,[],[f43,f101])).

fof(f43,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f99,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f44,f96])).

fof(f44,plain,(
    m1_pre_topc(sK3,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f94,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f45,f91])).

fof(f45,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f89,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f46,f86])).

fof(f46,plain,(
    m1_pre_topc(sK4,sK1) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f47,f81])).

fof(f47,plain,(
    m1_pre_topc(sK2,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f79,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f48,f76])).

fof(f48,plain,(
    m1_pre_topc(sK3,sK4) ),
    inference(cnf_transformation,[],[f33])).

fof(f74,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f49,f71])).

fof(f49,plain,(
    ~ r1_tsep_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f33])).

fof(f69,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f50,f66])).

fof(f50,plain,(
    ~ m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK4) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:53 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (3567)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.46  % (3559)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.47  % (3564)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.47  % (3563)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.47  % (3567)Refutation not found, incomplete strategy% (3567)------------------------------
% 0.21/0.47  % (3567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (3567)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (3567)Memory used [KB]: 10618
% 0.21/0.47  % (3567)Time elapsed: 0.065 s
% 0.21/0.47  % (3567)------------------------------
% 0.21/0.47  % (3567)------------------------------
% 0.21/0.48  % (3556)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (3555)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  % (3553)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (3560)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (3561)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.49  % (3558)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (3557)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.49  % (3557)Refutation not found, incomplete strategy% (3557)------------------------------
% 0.21/0.49  % (3557)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (3557)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (3557)Memory used [KB]: 6140
% 0.21/0.49  % (3557)Time elapsed: 0.085 s
% 0.21/0.49  % (3557)------------------------------
% 0.21/0.49  % (3557)------------------------------
% 0.21/0.49  % (3552)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (3547)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (3562)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (3548)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (3548)Refutation not found, incomplete strategy% (3548)------------------------------
% 0.21/0.50  % (3548)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (3548)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (3548)Memory used [KB]: 10618
% 0.21/0.50  % (3548)Time elapsed: 0.069 s
% 0.21/0.50  % (3548)------------------------------
% 0.21/0.50  % (3548)------------------------------
% 0.21/0.50  % (3565)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  % (3549)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.50  % (3551)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.51  % (3550)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (3554)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.52  % (3566)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.54  % (3563)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.54  % SZS output start Proof for theBenchmark
% 0.21/0.55  fof(f3985,plain,(
% 0.21/0.55    $false),
% 0.21/0.55    inference(avatar_sat_refutation,[],[f69,f74,f79,f84,f89,f94,f99,f104,f109,f114,f119,f124,f129,f156,f192,f259,f299,f458,f463,f468,f630,f774,f779,f784,f1333,f1409,f1421,f2940,f3839,f3983])).
% 0.21/0.55  fof(f3983,plain,(
% 0.21/0.55    ~spl5_16 | ~spl5_19 | ~spl5_112 | spl5_207 | ~spl5_448 | ~spl5_583),
% 0.21/0.55    inference(avatar_contradiction_clause,[],[f3982])).
% 0.21/0.55  fof(f3982,plain,(
% 0.21/0.55    $false | (~spl5_16 | ~spl5_19 | ~spl5_112 | spl5_207 | ~spl5_448 | ~spl5_583)),
% 0.21/0.55    inference(subsumption_resolution,[],[f3981,f1420])).
% 0.21/0.55  fof(f1420,plain,(
% 0.21/0.55    ~r1_tarski(k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)),u1_struct_0(sK4)) | spl5_207),
% 0.21/0.55    inference(avatar_component_clause,[],[f1418])).
% 0.21/0.55  fof(f1418,plain,(
% 0.21/0.55    spl5_207 <=> r1_tarski(k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)),u1_struct_0(sK4))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_207])])).
% 0.21/0.55  fof(f3981,plain,(
% 0.21/0.55    r1_tarski(k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)),u1_struct_0(sK4)) | (~spl5_16 | ~spl5_19 | ~spl5_112 | ~spl5_448 | ~spl5_583)),
% 0.21/0.55    inference(forward_demodulation,[],[f3872,f2939])).
% 0.21/0.55  fof(f2939,plain,(
% 0.21/0.55    k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK4,sK2,sK3)) | ~spl5_448),
% 0.21/0.55    inference(avatar_component_clause,[],[f2937])).
% 0.21/0.55  fof(f2937,plain,(
% 0.21/0.55    spl5_448 <=> k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK4,sK2,sK3))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_448])])).
% 0.21/0.55  fof(f3872,plain,(
% 0.21/0.55    r1_tarski(u1_struct_0(k2_tsep_1(sK4,sK2,sK3)),u1_struct_0(sK4)) | (~spl5_16 | ~spl5_19 | ~spl5_112 | ~spl5_583)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f184,f151,f783,f783,f3838,f59])).
% 0.21/0.55  fof(f59,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f35])).
% 0.21/0.55  fof(f35,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f24])).
% 0.21/0.55  fof(f24,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f23])).
% 0.21/0.55  fof(f23,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f8])).
% 0.21/0.55  fof(f8,axiom,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 0.21/0.55  fof(f3838,plain,(
% 0.21/0.55    m1_pre_topc(sK4,sK4) | ~spl5_583),
% 0.21/0.55    inference(avatar_component_clause,[],[f3836])).
% 0.21/0.55  fof(f3836,plain,(
% 0.21/0.55    spl5_583 <=> m1_pre_topc(sK4,sK4)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_583])])).
% 0.21/0.55  fof(f783,plain,(
% 0.21/0.55    m1_pre_topc(k2_tsep_1(sK4,sK2,sK3),sK4) | ~spl5_112),
% 0.21/0.55    inference(avatar_component_clause,[],[f781])).
% 0.21/0.55  fof(f781,plain,(
% 0.21/0.55    spl5_112 <=> m1_pre_topc(k2_tsep_1(sK4,sK2,sK3),sK4)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_112])])).
% 0.21/0.55  fof(f151,plain,(
% 0.21/0.55    l1_pre_topc(sK4) | ~spl5_16),
% 0.21/0.55    inference(avatar_component_clause,[],[f149])).
% 0.21/0.55  fof(f149,plain,(
% 0.21/0.55    spl5_16 <=> l1_pre_topc(sK4)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.55  fof(f184,plain,(
% 0.21/0.55    v2_pre_topc(sK4) | ~spl5_19),
% 0.21/0.55    inference(avatar_component_clause,[],[f182])).
% 0.21/0.55  fof(f182,plain,(
% 0.21/0.55    spl5_19 <=> v2_pre_topc(sK4)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_19])])).
% 0.21/0.55  fof(f3839,plain,(
% 0.21/0.55    spl5_583 | ~spl5_5 | spl5_6 | ~spl5_11 | ~spl5_12 | spl5_13 | ~spl5_87),
% 0.21/0.55    inference(avatar_split_clause,[],[f3825,f627,f126,f121,f116,f91,f86,f3836])).
% 0.21/0.55  fof(f86,plain,(
% 0.21/0.55    spl5_5 <=> m1_pre_topc(sK4,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.55  fof(f91,plain,(
% 0.21/0.55    spl5_6 <=> v2_struct_0(sK4)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.55  fof(f116,plain,(
% 0.21/0.55    spl5_11 <=> l1_pre_topc(sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 0.21/0.55  fof(f121,plain,(
% 0.21/0.55    spl5_12 <=> v2_pre_topc(sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 0.21/0.55  fof(f126,plain,(
% 0.21/0.55    spl5_13 <=> v2_struct_0(sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.55  fof(f627,plain,(
% 0.21/0.55    spl5_87 <=> m1_pre_topc(sK4,k1_tsep_1(sK1,sK4,sK4))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).
% 0.21/0.55  fof(f3825,plain,(
% 0.21/0.55    m1_pre_topc(sK4,sK4) | (~spl5_5 | spl5_6 | ~spl5_11 | ~spl5_12 | spl5_13 | ~spl5_87)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f128,f123,f118,f93,f88,f629,f339])).
% 0.21/0.55  fof(f339,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,k1_tsep_1(X1,X0,X0)) | m1_pre_topc(X2,X0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.55    inference(subsumption_resolution,[],[f311,f51])).
% 0.21/0.55  fof(f51,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | l1_pre_topc(X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f13])).
% 0.21/0.55  fof(f13,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f2])).
% 0.21/0.55  fof(f2,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.55  fof(f311,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~m1_pre_topc(X2,k1_tsep_1(X1,X0,X0)) | m1_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X0,X1) | v2_struct_0(X0) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) )),
% 0.21/0.55    inference(superposition,[],[f52,f53])).
% 0.21/0.55  fof(f53,plain,(
% 0.21/0.55    ( ! [X0,X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f16])).
% 0.21/0.55  fof(f16,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f15])).
% 0.21/0.55  fof(f15,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f7])).
% 0.21/0.55  fof(f7,axiom,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => k1_tsep_1(X0,X1,X1) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_tmap_1)).
% 0.21/0.55  fof(f52,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) | m1_pre_topc(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f14])).
% 0.21/0.55  fof(f14,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (m1_pre_topc(X1,X0) | ~m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.55    inference(ennf_transformation,[],[f3])).
% 0.21/0.55  fof(f3,axiom,(
% 0.21/0.55    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))) => m1_pre_topc(X1,X0)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_pre_topc)).
% 0.21/0.55  fof(f629,plain,(
% 0.21/0.55    m1_pre_topc(sK4,k1_tsep_1(sK1,sK4,sK4)) | ~spl5_87),
% 0.21/0.55    inference(avatar_component_clause,[],[f627])).
% 0.21/0.55  fof(f88,plain,(
% 0.21/0.55    m1_pre_topc(sK4,sK1) | ~spl5_5),
% 0.21/0.55    inference(avatar_component_clause,[],[f86])).
% 0.21/0.55  fof(f93,plain,(
% 0.21/0.55    ~v2_struct_0(sK4) | spl5_6),
% 0.21/0.55    inference(avatar_component_clause,[],[f91])).
% 0.21/0.55  fof(f118,plain,(
% 0.21/0.55    l1_pre_topc(sK1) | ~spl5_11),
% 0.21/0.55    inference(avatar_component_clause,[],[f116])).
% 0.21/0.55  fof(f123,plain,(
% 0.21/0.55    v2_pre_topc(sK1) | ~spl5_12),
% 0.21/0.55    inference(avatar_component_clause,[],[f121])).
% 0.21/0.55  fof(f128,plain,(
% 0.21/0.55    ~v2_struct_0(sK1) | spl5_13),
% 0.21/0.55    inference(avatar_component_clause,[],[f126])).
% 0.21/0.55  fof(f2940,plain,(
% 0.21/0.55    spl5_448 | spl5_2 | ~spl5_3 | ~spl5_4 | spl5_6 | spl5_8 | spl5_10 | ~spl5_16 | spl5_110 | ~spl5_111 | ~spl5_112),
% 0.21/0.55    inference(avatar_split_clause,[],[f2813,f781,f776,f771,f149,f111,f101,f91,f81,f76,f71,f2937])).
% 0.21/0.55  fof(f71,plain,(
% 0.21/0.55    spl5_2 <=> r1_tsep_1(sK2,sK3)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.55  fof(f76,plain,(
% 0.21/0.55    spl5_3 <=> m1_pre_topc(sK3,sK4)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.55  fof(f81,plain,(
% 0.21/0.55    spl5_4 <=> m1_pre_topc(sK2,sK4)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.55  fof(f101,plain,(
% 0.21/0.55    spl5_8 <=> v2_struct_0(sK3)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 0.21/0.55  fof(f111,plain,(
% 0.21/0.55    spl5_10 <=> v2_struct_0(sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 0.21/0.55  fof(f771,plain,(
% 0.21/0.55    spl5_110 <=> v2_struct_0(k2_tsep_1(sK4,sK2,sK3))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_110])])).
% 0.21/0.55  fof(f776,plain,(
% 0.21/0.55    spl5_111 <=> v1_pre_topc(k2_tsep_1(sK4,sK2,sK3))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_111])])).
% 0.21/0.55  fof(f2813,plain,(
% 0.21/0.55    k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) = u1_struct_0(k2_tsep_1(sK4,sK2,sK3)) | (spl5_2 | ~spl5_3 | ~spl5_4 | spl5_6 | spl5_8 | spl5_10 | ~spl5_16 | spl5_110 | ~spl5_111 | ~spl5_112)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f93,f151,f113,f103,f83,f78,f73,f773,f778,f783,f64])).
% 0.21/0.55  fof(f64,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(equality_resolution,[],[f55])).
% 0.21/0.55  fof(f55,plain,(
% 0.21/0.55    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f34])).
% 0.21/0.55  fof(f34,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(nnf_transformation,[],[f20])).
% 0.21/0.55  fof(f20,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f19])).
% 0.21/0.55  fof(f19,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f4])).
% 0.21/0.55  fof(f4,axiom,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).
% 0.21/0.55  fof(f778,plain,(
% 0.21/0.55    v1_pre_topc(k2_tsep_1(sK4,sK2,sK3)) | ~spl5_111),
% 0.21/0.55    inference(avatar_component_clause,[],[f776])).
% 0.21/0.55  fof(f773,plain,(
% 0.21/0.55    ~v2_struct_0(k2_tsep_1(sK4,sK2,sK3)) | spl5_110),
% 0.21/0.55    inference(avatar_component_clause,[],[f771])).
% 0.21/0.55  fof(f73,plain,(
% 0.21/0.55    ~r1_tsep_1(sK2,sK3) | spl5_2),
% 0.21/0.55    inference(avatar_component_clause,[],[f71])).
% 0.21/0.55  fof(f78,plain,(
% 0.21/0.55    m1_pre_topc(sK3,sK4) | ~spl5_3),
% 0.21/0.55    inference(avatar_component_clause,[],[f76])).
% 0.21/0.55  fof(f83,plain,(
% 0.21/0.55    m1_pre_topc(sK2,sK4) | ~spl5_4),
% 0.21/0.55    inference(avatar_component_clause,[],[f81])).
% 0.21/0.55  fof(f103,plain,(
% 0.21/0.55    ~v2_struct_0(sK3) | spl5_8),
% 0.21/0.55    inference(avatar_component_clause,[],[f101])).
% 0.21/0.55  fof(f113,plain,(
% 0.21/0.55    ~v2_struct_0(sK2) | spl5_10),
% 0.21/0.55    inference(avatar_component_clause,[],[f111])).
% 0.21/0.55  fof(f1421,plain,(
% 0.21/0.55    ~spl5_207 | spl5_190 | ~spl5_205),
% 0.21/0.55    inference(avatar_split_clause,[],[f1416,f1406,f1330,f1418])).
% 0.21/0.55  fof(f1330,plain,(
% 0.21/0.55    spl5_190 <=> r1_tarski(u1_struct_0(k2_tsep_1(sK1,sK2,sK3)),u1_struct_0(sK4))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_190])])).
% 0.21/0.55  fof(f1406,plain,(
% 0.21/0.55    spl5_205 <=> u1_struct_0(k2_tsep_1(sK1,sK2,sK3)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_205])])).
% 0.21/0.55  fof(f1416,plain,(
% 0.21/0.55    ~r1_tarski(k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)),u1_struct_0(sK4)) | (spl5_190 | ~spl5_205)),
% 0.21/0.55    inference(forward_demodulation,[],[f1332,f1408])).
% 0.21/0.55  fof(f1408,plain,(
% 0.21/0.55    u1_struct_0(k2_tsep_1(sK1,sK2,sK3)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) | ~spl5_205),
% 0.21/0.55    inference(avatar_component_clause,[],[f1406])).
% 0.21/0.55  fof(f1332,plain,(
% 0.21/0.55    ~r1_tarski(u1_struct_0(k2_tsep_1(sK1,sK2,sK3)),u1_struct_0(sK4)) | spl5_190),
% 0.21/0.55    inference(avatar_component_clause,[],[f1330])).
% 0.21/0.55  fof(f1409,plain,(
% 0.21/0.55    spl5_205 | spl5_2 | ~spl5_7 | spl5_8 | ~spl5_9 | spl5_10 | ~spl5_11 | spl5_13 | spl5_59 | ~spl5_60 | ~spl5_61),
% 0.21/0.55    inference(avatar_split_clause,[],[f1228,f465,f460,f455,f126,f116,f111,f106,f101,f96,f71,f1406])).
% 0.21/0.55  fof(f96,plain,(
% 0.21/0.55    spl5_7 <=> m1_pre_topc(sK3,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 0.21/0.55  fof(f106,plain,(
% 0.21/0.55    spl5_9 <=> m1_pre_topc(sK2,sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 0.21/0.55  fof(f455,plain,(
% 0.21/0.55    spl5_59 <=> v2_struct_0(k2_tsep_1(sK1,sK2,sK3))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_59])])).
% 0.21/0.55  fof(f460,plain,(
% 0.21/0.55    spl5_60 <=> v1_pre_topc(k2_tsep_1(sK1,sK2,sK3))),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).
% 0.21/0.55  fof(f465,plain,(
% 0.21/0.55    spl5_61 <=> m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK1)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).
% 0.21/0.55  fof(f1228,plain,(
% 0.21/0.55    u1_struct_0(k2_tsep_1(sK1,sK2,sK3)) = k3_xboole_0(u1_struct_0(sK2),u1_struct_0(sK3)) | (spl5_2 | ~spl5_7 | spl5_8 | ~spl5_9 | spl5_10 | ~spl5_11 | spl5_13 | spl5_59 | ~spl5_60 | ~spl5_61)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f128,f118,f113,f103,f108,f98,f73,f457,f462,f467,f64])).
% 0.21/0.55  fof(f467,plain,(
% 0.21/0.55    m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK1) | ~spl5_61),
% 0.21/0.55    inference(avatar_component_clause,[],[f465])).
% 0.21/0.55  fof(f462,plain,(
% 0.21/0.55    v1_pre_topc(k2_tsep_1(sK1,sK2,sK3)) | ~spl5_60),
% 0.21/0.55    inference(avatar_component_clause,[],[f460])).
% 0.21/0.55  fof(f457,plain,(
% 0.21/0.55    ~v2_struct_0(k2_tsep_1(sK1,sK2,sK3)) | spl5_59),
% 0.21/0.55    inference(avatar_component_clause,[],[f455])).
% 0.21/0.55  fof(f98,plain,(
% 0.21/0.55    m1_pre_topc(sK3,sK1) | ~spl5_7),
% 0.21/0.55    inference(avatar_component_clause,[],[f96])).
% 0.21/0.55  fof(f108,plain,(
% 0.21/0.55    m1_pre_topc(sK2,sK1) | ~spl5_9),
% 0.21/0.55    inference(avatar_component_clause,[],[f106])).
% 0.21/0.55  fof(f1333,plain,(
% 0.21/0.55    ~spl5_190 | spl5_1 | ~spl5_5 | ~spl5_11 | ~spl5_12 | ~spl5_61),
% 0.21/0.55    inference(avatar_split_clause,[],[f1246,f465,f121,f116,f86,f66,f1330])).
% 0.21/0.55  fof(f66,plain,(
% 0.21/0.55    spl5_1 <=> m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK4)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.55  fof(f1246,plain,(
% 0.21/0.55    ~r1_tarski(u1_struct_0(k2_tsep_1(sK1,sK2,sK3)),u1_struct_0(sK4)) | (spl5_1 | ~spl5_5 | ~spl5_11 | ~spl5_12 | ~spl5_61)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f123,f118,f88,f68,f467,f58])).
% 0.21/0.55  fof(f58,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f35])).
% 0.21/0.55  fof(f68,plain,(
% 0.21/0.55    ~m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK4) | spl5_1),
% 0.21/0.55    inference(avatar_component_clause,[],[f66])).
% 0.21/0.55  fof(f784,plain,(
% 0.21/0.55    spl5_112 | ~spl5_34),
% 0.21/0.55    inference(avatar_split_clause,[],[f767,f296,f781])).
% 0.21/0.55  fof(f296,plain,(
% 0.21/0.55    spl5_34 <=> sP0(sK4,sK3,sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 0.21/0.55  fof(f767,plain,(
% 0.21/0.55    m1_pre_topc(k2_tsep_1(sK4,sK2,sK3),sK4) | ~spl5_34),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f298,f62])).
% 0.21/0.55  fof(f62,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X2,X1),X0) | ~sP0(X0,X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f37])).
% 0.21/0.55  fof(f37,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X2,X1),X0) & v1_pre_topc(k2_tsep_1(X0,X2,X1)) & ~v2_struct_0(k2_tsep_1(X0,X2,X1))) | ~sP0(X0,X1,X2))),
% 0.21/0.55    inference(rectify,[],[f36])).
% 0.21/0.55  fof(f36,plain,(
% 0.21/0.55    ! [X0,X2,X1] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~sP0(X0,X2,X1))),
% 0.21/0.55    inference(nnf_transformation,[],[f27])).
% 0.21/0.55  fof(f27,plain,(
% 0.21/0.55    ! [X0,X2,X1] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~sP0(X0,X2,X1))),
% 0.21/0.55    introduced(predicate_definition_introduction,[new_symbols(naming,[sP0])])).
% 0.21/0.55  fof(f298,plain,(
% 0.21/0.55    sP0(sK4,sK3,sK2) | ~spl5_34),
% 0.21/0.55    inference(avatar_component_clause,[],[f296])).
% 0.21/0.55  fof(f779,plain,(
% 0.21/0.55    spl5_111 | ~spl5_34),
% 0.21/0.55    inference(avatar_split_clause,[],[f768,f296,f776])).
% 0.21/0.55  fof(f768,plain,(
% 0.21/0.55    v1_pre_topc(k2_tsep_1(sK4,sK2,sK3)) | ~spl5_34),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f298,f61])).
% 0.21/0.55  fof(f61,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (v1_pre_topc(k2_tsep_1(X0,X2,X1)) | ~sP0(X0,X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f37])).
% 0.21/0.55  fof(f774,plain,(
% 0.21/0.55    ~spl5_110 | ~spl5_34),
% 0.21/0.55    inference(avatar_split_clause,[],[f769,f296,f771])).
% 0.21/0.55  fof(f769,plain,(
% 0.21/0.55    ~v2_struct_0(k2_tsep_1(sK4,sK2,sK3)) | ~spl5_34),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f298,f60])).
% 0.21/0.55  fof(f60,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X2,X1)) | ~sP0(X0,X1,X2)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f37])).
% 0.21/0.55  fof(f630,plain,(
% 0.21/0.55    spl5_87 | ~spl5_5 | spl5_6 | ~spl5_11 | ~spl5_12 | spl5_13),
% 0.21/0.55    inference(avatar_split_clause,[],[f573,f126,f121,f116,f91,f86,f627])).
% 0.21/0.55  fof(f573,plain,(
% 0.21/0.55    m1_pre_topc(sK4,k1_tsep_1(sK1,sK4,sK4)) | (~spl5_5 | spl5_6 | ~spl5_11 | ~spl5_12 | spl5_13)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f128,f123,f118,f93,f88,f93,f88,f54])).
% 0.21/0.55  fof(f54,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f18])).
% 0.21/0.55  fof(f18,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f17])).
% 0.21/0.55  fof(f17,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (! [X2] : (m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f6])).
% 0.21/0.55  fof(f6,axiom,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => m1_pre_topc(X1,k1_tsep_1(X0,X1,X2)))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_tsep_1)).
% 0.21/0.55  fof(f468,plain,(
% 0.21/0.55    spl5_61 | ~spl5_26),
% 0.21/0.55    inference(avatar_split_clause,[],[f451,f256,f465])).
% 0.21/0.55  fof(f256,plain,(
% 0.21/0.55    spl5_26 <=> sP0(sK1,sK3,sK2)),
% 0.21/0.55    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.55  fof(f451,plain,(
% 0.21/0.55    m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK1) | ~spl5_26),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f258,f62])).
% 0.21/0.55  fof(f258,plain,(
% 0.21/0.55    sP0(sK1,sK3,sK2) | ~spl5_26),
% 0.21/0.55    inference(avatar_component_clause,[],[f256])).
% 0.21/0.55  fof(f463,plain,(
% 0.21/0.55    spl5_60 | ~spl5_26),
% 0.21/0.55    inference(avatar_split_clause,[],[f452,f256,f460])).
% 0.21/0.55  fof(f452,plain,(
% 0.21/0.55    v1_pre_topc(k2_tsep_1(sK1,sK2,sK3)) | ~spl5_26),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f258,f61])).
% 0.21/0.55  fof(f458,plain,(
% 0.21/0.55    ~spl5_59 | ~spl5_26),
% 0.21/0.55    inference(avatar_split_clause,[],[f453,f256,f455])).
% 0.21/0.55  fof(f453,plain,(
% 0.21/0.55    ~v2_struct_0(k2_tsep_1(sK1,sK2,sK3)) | ~spl5_26),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f258,f60])).
% 0.21/0.55  fof(f299,plain,(
% 0.21/0.55    spl5_34 | ~spl5_3 | ~spl5_4 | spl5_6 | spl5_8 | spl5_10 | ~spl5_16),
% 0.21/0.55    inference(avatar_split_clause,[],[f228,f149,f111,f101,f91,f81,f76,f296])).
% 0.21/0.55  fof(f228,plain,(
% 0.21/0.55    sP0(sK4,sK3,sK2) | (~spl5_3 | ~spl5_4 | spl5_6 | spl5_8 | spl5_10 | ~spl5_16)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f93,f151,f113,f83,f103,f78,f63])).
% 0.21/0.55  fof(f63,plain,(
% 0.21/0.55    ( ! [X2,X0,X1] : (sP0(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f28])).
% 0.21/0.55  fof(f28,plain,(
% 0.21/0.55    ! [X0,X1,X2] : (sP0(X0,X2,X1) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(definition_folding,[],[f26,f27])).
% 0.21/0.55  fof(f26,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f25])).
% 0.21/0.55  fof(f25,plain,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f5])).
% 0.21/0.55  fof(f5,axiom,(
% 0.21/0.55    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 0.21/0.55  fof(f259,plain,(
% 0.21/0.55    spl5_26 | ~spl5_7 | spl5_8 | ~spl5_9 | spl5_10 | ~spl5_11 | spl5_13),
% 0.21/0.55    inference(avatar_split_clause,[],[f236,f126,f116,f111,f106,f101,f96,f256])).
% 0.21/0.55  fof(f236,plain,(
% 0.21/0.55    sP0(sK1,sK3,sK2) | (~spl5_7 | spl5_8 | ~spl5_9 | spl5_10 | ~spl5_11 | spl5_13)),
% 0.21/0.55    inference(unit_resulting_resolution,[],[f128,f118,f113,f108,f103,f98,f63])).
% 0.21/0.55  fof(f192,plain,(
% 0.21/0.55    spl5_19 | ~spl5_5 | ~spl5_11 | ~spl5_12),
% 0.21/0.55    inference(avatar_split_clause,[],[f191,f121,f116,f86,f182])).
% 0.21/0.55  fof(f191,plain,(
% 0.21/0.55    v2_pre_topc(sK4) | (~spl5_5 | ~spl5_11 | ~spl5_12)),
% 0.21/0.55    inference(subsumption_resolution,[],[f190,f123])).
% 0.21/0.55  fof(f190,plain,(
% 0.21/0.55    v2_pre_topc(sK4) | ~v2_pre_topc(sK1) | (~spl5_5 | ~spl5_11)),
% 0.21/0.55    inference(subsumption_resolution,[],[f168,f118])).
% 0.21/0.55  fof(f168,plain,(
% 0.21/0.55    v2_pre_topc(sK4) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | ~spl5_5),
% 0.21/0.55    inference(resolution,[],[f57,f88])).
% 0.21/0.55  fof(f57,plain,(
% 0.21/0.55    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | v2_pre_topc(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.55    inference(cnf_transformation,[],[f22])).
% 0.21/0.55  fof(f22,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.55    inference(flattening,[],[f21])).
% 0.21/0.55  fof(f21,plain,(
% 0.21/0.55    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f1])).
% 0.21/0.55  fof(f1,axiom,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.21/0.55  fof(f156,plain,(
% 0.21/0.55    spl5_16 | ~spl5_5 | ~spl5_11),
% 0.21/0.55    inference(avatar_split_clause,[],[f155,f116,f86,f149])).
% 0.21/0.55  fof(f155,plain,(
% 0.21/0.55    l1_pre_topc(sK4) | (~spl5_5 | ~spl5_11)),
% 0.21/0.55    inference(subsumption_resolution,[],[f135,f118])).
% 0.21/0.55  fof(f135,plain,(
% 0.21/0.55    l1_pre_topc(sK4) | ~l1_pre_topc(sK1) | ~spl5_5),
% 0.21/0.55    inference(resolution,[],[f51,f88])).
% 0.21/0.55  fof(f129,plain,(
% 0.21/0.55    ~spl5_13),
% 0.21/0.55    inference(avatar_split_clause,[],[f38,f126])).
% 0.21/0.55  fof(f38,plain,(
% 0.21/0.55    ~v2_struct_0(sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f33,plain,(
% 0.21/0.55    (((~m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK4) & ~r1_tsep_1(sK2,sK3) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK2,sK4) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1)),
% 0.21/0.55    inference(skolemisation,[status(esa),new_symbols(skolem,[sK1,sK2,sK3,sK4])],[f12,f32,f31,f30,f29])).
% 0.21/0.55  fof(f29,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK1,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) & l1_pre_topc(sK1) & v2_pre_topc(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f30,plain,(
% 0.21/0.55    ? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK1,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK1) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK1,sK2,X2),X3) & ~r1_tsep_1(sK2,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(sK2,X3) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) & m1_pre_topc(sK2,sK1) & ~v2_struct_0(sK2))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f31,plain,(
% 0.21/0.55    ? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(sK1,sK2,X2),X3) & ~r1_tsep_1(sK2,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(sK2,X3) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK1) & ~v2_struct_0(X2)) => (? [X3] : (~m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),X3) & ~r1_tsep_1(sK2,sK3) & m1_pre_topc(sK3,X3) & m1_pre_topc(sK2,X3) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) & m1_pre_topc(sK3,sK1) & ~v2_struct_0(sK3))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f32,plain,(
% 0.21/0.55    ? [X3] : (~m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),X3) & ~r1_tsep_1(sK2,sK3) & m1_pre_topc(sK3,X3) & m1_pre_topc(sK2,X3) & m1_pre_topc(X3,sK1) & ~v2_struct_0(X3)) => (~m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK4) & ~r1_tsep_1(sK2,sK3) & m1_pre_topc(sK3,sK4) & m1_pre_topc(sK2,sK4) & m1_pre_topc(sK4,sK1) & ~v2_struct_0(sK4))),
% 0.21/0.55    introduced(choice_axiom,[])).
% 0.21/0.55  fof(f12,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.55    inference(flattening,[],[f11])).
% 0.21/0.55  fof(f11,plain,(
% 0.21/0.55    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (((~m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.55    inference(ennf_transformation,[],[f10])).
% 0.21/0.55  fof(f10,negated_conjecture,(
% 0.21/0.55    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))))))),
% 0.21/0.55    inference(negated_conjecture,[],[f9])).
% 0.21/0.55  fof(f9,conjecture,(
% 0.21/0.55    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ((m1_pre_topc(X2,X3) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X3) | r1_tsep_1(X1,X2)))))))),
% 0.21/0.55    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_tmap_1)).
% 0.21/0.55  fof(f124,plain,(
% 0.21/0.55    spl5_12),
% 0.21/0.55    inference(avatar_split_clause,[],[f39,f121])).
% 0.21/0.55  fof(f39,plain,(
% 0.21/0.55    v2_pre_topc(sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f119,plain,(
% 0.21/0.55    spl5_11),
% 0.21/0.55    inference(avatar_split_clause,[],[f40,f116])).
% 0.21/0.55  fof(f40,plain,(
% 0.21/0.55    l1_pre_topc(sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f114,plain,(
% 0.21/0.55    ~spl5_10),
% 0.21/0.55    inference(avatar_split_clause,[],[f41,f111])).
% 0.21/0.55  fof(f41,plain,(
% 0.21/0.55    ~v2_struct_0(sK2)),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f109,plain,(
% 0.21/0.55    spl5_9),
% 0.21/0.55    inference(avatar_split_clause,[],[f42,f106])).
% 0.21/0.55  fof(f42,plain,(
% 0.21/0.55    m1_pre_topc(sK2,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f104,plain,(
% 0.21/0.55    ~spl5_8),
% 0.21/0.55    inference(avatar_split_clause,[],[f43,f101])).
% 0.21/0.55  fof(f43,plain,(
% 0.21/0.55    ~v2_struct_0(sK3)),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f99,plain,(
% 0.21/0.55    spl5_7),
% 0.21/0.55    inference(avatar_split_clause,[],[f44,f96])).
% 0.21/0.55  fof(f44,plain,(
% 0.21/0.55    m1_pre_topc(sK3,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f94,plain,(
% 0.21/0.55    ~spl5_6),
% 0.21/0.55    inference(avatar_split_clause,[],[f45,f91])).
% 0.21/0.55  fof(f45,plain,(
% 0.21/0.55    ~v2_struct_0(sK4)),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f89,plain,(
% 0.21/0.55    spl5_5),
% 0.21/0.55    inference(avatar_split_clause,[],[f46,f86])).
% 0.21/0.55  fof(f46,plain,(
% 0.21/0.55    m1_pre_topc(sK4,sK1)),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f84,plain,(
% 0.21/0.55    spl5_4),
% 0.21/0.55    inference(avatar_split_clause,[],[f47,f81])).
% 0.21/0.55  fof(f47,plain,(
% 0.21/0.55    m1_pre_topc(sK2,sK4)),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f79,plain,(
% 0.21/0.55    spl5_3),
% 0.21/0.55    inference(avatar_split_clause,[],[f48,f76])).
% 0.21/0.55  fof(f48,plain,(
% 0.21/0.55    m1_pre_topc(sK3,sK4)),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f74,plain,(
% 0.21/0.55    ~spl5_2),
% 0.21/0.55    inference(avatar_split_clause,[],[f49,f71])).
% 0.21/0.55  fof(f49,plain,(
% 0.21/0.55    ~r1_tsep_1(sK2,sK3)),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  fof(f69,plain,(
% 0.21/0.55    ~spl5_1),
% 0.21/0.55    inference(avatar_split_clause,[],[f50,f66])).
% 0.21/0.55  fof(f50,plain,(
% 0.21/0.55    ~m1_pre_topc(k2_tsep_1(sK1,sK2,sK3),sK4)),
% 0.21/0.55    inference(cnf_transformation,[],[f33])).
% 0.21/0.55  % SZS output end Proof for theBenchmark
% 0.21/0.55  % (3563)------------------------------
% 0.21/0.55  % (3563)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (3563)Termination reason: Refutation
% 0.21/0.55  
% 0.21/0.55  % (3563)Memory used [KB]: 14072
% 0.21/0.55  % (3563)Time elapsed: 0.131 s
% 0.21/0.55  % (3563)------------------------------
% 0.21/0.55  % (3563)------------------------------
% 0.21/0.55  % (3546)Success in time 0.193 s
%------------------------------------------------------------------------------
