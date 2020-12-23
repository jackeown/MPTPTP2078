%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:18:02 EST 2020

% Result     : Theorem 1.51s
% Output     : Refutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :  165 ( 437 expanded)
%              Number of leaves         :   43 ( 234 expanded)
%              Depth                    :   11
%              Number of atoms          :  914 (3925 expanded)
%              Number of equality atoms :   33 (  46 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f1051,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f59,f63,f67,f71,f75,f79,f83,f87,f91,f95,f99,f103,f107,f111,f115,f125,f134,f140,f168,f361,f829,f873,f897,f977,f988,f1003,f1025,f1026,f1034,f1037,f1046,f1048,f1050])).

fof(f1050,plain,
    ( spl5_15
    | ~ spl5_13
    | spl5_8
    | ~ spl5_7
    | spl5_6
    | ~ spl5_5
    | spl5_178 ),
    inference(avatar_split_clause,[],[f1049,f1044,f73,f77,f81,f85,f105,f113])).

fof(f113,plain,
    ( spl5_15
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f105,plain,
    ( spl5_13
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f85,plain,
    ( spl5_8
  <=> v2_struct_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).

fof(f81,plain,
    ( spl5_7
  <=> m1_pre_topc(sK3,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).

fof(f77,plain,
    ( spl5_6
  <=> v2_struct_0(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f73,plain,
    ( spl5_5
  <=> m1_pre_topc(sK4,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f1044,plain,
    ( spl5_178
  <=> m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_178])])).

fof(f1049,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | v2_struct_0(sK4)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_178 ),
    inference(resolution,[],[f1045,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( m1_pre_topc(k2_tsep_1(X0,X1,X2),X0)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
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

fof(f1045,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),sK0)
    | spl5_178 ),
    inference(avatar_component_clause,[],[f1044])).

fof(f1048,plain,
    ( spl5_15
    | ~ spl5_13
    | spl5_12
    | ~ spl5_11
    | spl5_10
    | ~ spl5_9
    | spl5_177 ),
    inference(avatar_split_clause,[],[f1047,f1041,f89,f93,f97,f101,f105,f113])).

fof(f101,plain,
    ( spl5_12
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f97,plain,
    ( spl5_11
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).

fof(f93,plain,
    ( spl5_10
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f89,plain,
    ( spl5_9
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f1041,plain,
    ( spl5_177
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_177])])).

fof(f1047,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK1)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | spl5_177 ),
    inference(resolution,[],[f1042,f53])).

fof(f1042,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | spl5_177 ),
    inference(avatar_component_clause,[],[f1041])).

fof(f1046,plain,
    ( ~ spl5_177
    | ~ spl5_13
    | ~ spl5_178
    | ~ spl5_14
    | ~ spl5_175 ),
    inference(avatar_split_clause,[],[f1039,f1022,f109,f1044,f105,f1041])).

fof(f109,plain,
    ( spl5_14
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f1022,plain,
    ( spl5_175
  <=> ! [X0] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_175])])).

fof(f1039,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl5_14
    | ~ spl5_175 ),
    inference(resolution,[],[f1023,f110])).

fof(f110,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f109])).

fof(f1023,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) )
    | ~ spl5_175 ),
    inference(avatar_component_clause,[],[f1022])).

fof(f1037,plain,
    ( ~ spl5_9
    | ~ spl5_13
    | ~ spl5_5
    | ~ spl5_14
    | ~ spl5_169 ),
    inference(avatar_split_clause,[],[f1036,f985,f109,f73,f105,f89])).

fof(f985,plain,
    ( spl5_169
  <=> ! [X0] :
        ( ~ m1_pre_topc(sK4,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_169])])).

fof(f1036,plain,
    ( ~ m1_pre_topc(sK4,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2,sK0)
    | ~ spl5_14
    | ~ spl5_169 ),
    inference(resolution,[],[f986,f110])).

fof(f986,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(sK4,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK2,X0) )
    | ~ spl5_169 ),
    inference(avatar_component_clause,[],[f985])).

fof(f1034,plain,
    ( ~ spl5_11
    | ~ spl5_13
    | ~ spl5_7
    | ~ spl5_14
    | ~ spl5_167 ),
    inference(avatar_split_clause,[],[f1033,f974,f109,f81,f105,f97])).

fof(f974,plain,
    ( spl5_167
  <=> ! [X0] :
        ( ~ m1_pre_topc(sK3,X0)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_167])])).

fof(f1033,plain,
    ( ~ m1_pre_topc(sK3,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ spl5_14
    | ~ spl5_167 ),
    inference(resolution,[],[f975,f110])).

fof(f975,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(X0)
        | ~ m1_pre_topc(sK3,X0)
        | ~ l1_pre_topc(X0)
        | ~ m1_pre_topc(sK1,X0) )
    | ~ spl5_167 ),
    inference(avatar_component_clause,[],[f974])).

fof(f1026,plain,
    ( ~ spl5_33
    | ~ spl5_164
    | spl5_165
    | ~ spl5_17
    | ~ spl5_153 ),
    inference(avatar_split_clause,[],[f1016,f892,f132,f965,f962,f218])).

fof(f218,plain,
    ( spl5_33
  <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).

fof(f962,plain,
    ( spl5_164
  <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_164])])).

fof(f965,plain,
    ( spl5_165
  <=> r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_165])])).

fof(f132,plain,
    ( spl5_17
  <=> k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).

fof(f892,plain,
    ( spl5_153
  <=> k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k2_tsep_1(sK0,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_153])])).

fof(f1016,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4)))
    | ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK4))
    | ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3))
    | ~ spl5_17
    | ~ spl5_153 ),
    inference(superposition,[],[f142,f893])).

fof(f893,plain,
    ( k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k2_tsep_1(sK0,sK3,sK4))
    | ~ spl5_153 ),
    inference(avatar_component_clause,[],[f892])).

fof(f142,plain,
    ( ! [X2,X3] :
        ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),k3_xboole_0(X2,X3))
        | ~ r1_tarski(u1_struct_0(sK2),X3)
        | ~ r1_tarski(u1_struct_0(sK1),X2) )
    | ~ spl5_17 ),
    inference(superposition,[],[f54,f133])).

fof(f133,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | ~ spl5_17 ),
    inference(avatar_component_clause,[],[f132])).

fof(f54,plain,(
    ! [X2,X0,X3,X1] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2,X3] :
      ( r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3))
      | ~ r1_tarski(X2,X3)
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( r1_tarski(X2,X3)
        & r1_tarski(X0,X1) )
     => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_xboole_1)).

fof(f1025,plain,
    ( spl5_175
    | spl5_1
    | ~ spl5_165 ),
    inference(avatar_split_clause,[],[f1020,f965,f57,f1022])).

fof(f57,plain,
    ( spl5_1
  <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f1020,plain,
    ( ! [X0] :
        ( m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK4))
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),X0)
        | ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl5_165 ),
    inference(resolution,[],[f966,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(nnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
              <=> m1_pre_topc(X1,X2) )
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f966,plain,
    ( r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4)))
    | ~ spl5_165 ),
    inference(avatar_component_clause,[],[f965])).

fof(f1003,plain,
    ( spl5_8
    | ~ spl5_7
    | ~ spl5_4
    | ~ spl5_24
    | ~ spl5_154 ),
    inference(avatar_split_clause,[],[f991,f895,f166,f69,f81,f85])).

fof(f69,plain,
    ( spl5_4
  <=> m1_pre_topc(sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f166,plain,
    ( spl5_24
  <=> ! [X0] :
        ( ~ r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f895,plain,
    ( spl5_154
  <=> r1_tsep_1(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_154])])).

fof(f991,plain,
    ( ~ m1_pre_topc(sK1,sK3)
    | ~ m1_pre_topc(sK3,sK0)
    | v2_struct_0(sK3)
    | ~ spl5_24
    | ~ spl5_154 ),
    inference(resolution,[],[f896,f167])).

fof(f167,plain,
    ( ! [X0] :
        ( ~ r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(sK1,X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0) )
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f166])).

fof(f896,plain,
    ( r1_tsep_1(sK3,sK2)
    | ~ spl5_154 ),
    inference(avatar_component_clause,[],[f895])).

fof(f988,plain,
    ( spl5_169
    | ~ spl5_3
    | spl5_164 ),
    inference(avatar_split_clause,[],[f983,f962,f65,f985])).

fof(f65,plain,
    ( spl5_3
  <=> m1_pre_topc(sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f983,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK2,sK4)
        | ~ m1_pre_topc(sK4,X0)
        | ~ m1_pre_topc(sK2,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | spl5_164 ),
    inference(resolution,[],[f963,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( r1_tarski(u1_struct_0(X1),u1_struct_0(X2))
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f963,plain,
    ( ~ r1_tarski(u1_struct_0(sK2),u1_struct_0(sK4))
    | spl5_164 ),
    inference(avatar_component_clause,[],[f962])).

fof(f977,plain,
    ( spl5_167
    | ~ spl5_4
    | spl5_33 ),
    inference(avatar_split_clause,[],[f972,f218,f69,f974])).

fof(f972,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(sK1,sK3)
        | ~ m1_pre_topc(sK3,X0)
        | ~ m1_pre_topc(sK1,X0)
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) )
    | spl5_33 ),
    inference(resolution,[],[f219,f50])).

fof(f219,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3))
    | spl5_33 ),
    inference(avatar_component_clause,[],[f218])).

fof(f897,plain,
    ( spl5_153
    | spl5_8
    | spl5_154
    | ~ spl5_7
    | ~ spl5_149 ),
    inference(avatar_split_clause,[],[f877,f871,f81,f895,f85,f892])).

fof(f871,plain,
    ( spl5_149
  <=> ! [X0] :
        ( k3_xboole_0(u1_struct_0(X0),u1_struct_0(sK4)) = u1_struct_0(k2_tsep_1(sK0,X0,sK4))
        | r1_tsep_1(X0,sK2)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_149])])).

fof(f877,plain,
    ( r1_tsep_1(sK3,sK2)
    | v2_struct_0(sK3)
    | k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k2_tsep_1(sK0,sK3,sK4))
    | ~ spl5_7
    | ~ spl5_149 ),
    inference(resolution,[],[f872,f82])).

fof(f82,plain,
    ( m1_pre_topc(sK3,sK0)
    | ~ spl5_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f872,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | r1_tsep_1(X0,sK2)
        | v2_struct_0(X0)
        | k3_xboole_0(u1_struct_0(X0),u1_struct_0(sK4)) = u1_struct_0(k2_tsep_1(sK0,X0,sK4)) )
    | ~ spl5_149 ),
    inference(avatar_component_clause,[],[f871])).

fof(f873,plain,
    ( ~ spl5_5
    | spl5_6
    | spl5_149
    | ~ spl5_3
    | ~ spl5_142 ),
    inference(avatar_split_clause,[],[f868,f827,f65,f871,f77,f73])).

fof(f827,plain,
    ( spl5_142
  <=> ! [X7,X6] :
        ( r1_tsep_1(X6,sK2)
        | k3_xboole_0(u1_struct_0(X6),u1_struct_0(X7)) = u1_struct_0(k2_tsep_1(sK0,X6,X7))
        | ~ m1_pre_topc(X6,sK0)
        | v2_struct_0(X6)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(sK2,X7)
        | ~ m1_pre_topc(X7,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_142])])).

fof(f868,plain,
    ( ! [X0] :
        ( k3_xboole_0(u1_struct_0(X0),u1_struct_0(sK4)) = u1_struct_0(k2_tsep_1(sK0,X0,sK4))
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v2_struct_0(sK4)
        | r1_tsep_1(X0,sK2)
        | ~ m1_pre_topc(sK4,sK0) )
    | ~ spl5_3
    | ~ spl5_142 ),
    inference(resolution,[],[f828,f66])).

fof(f66,plain,
    ( m1_pre_topc(sK2,sK4)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f65])).

fof(f828,plain,
    ( ! [X6,X7] :
        ( ~ m1_pre_topc(sK2,X7)
        | k3_xboole_0(u1_struct_0(X6),u1_struct_0(X7)) = u1_struct_0(k2_tsep_1(sK0,X6,X7))
        | ~ m1_pre_topc(X6,sK0)
        | v2_struct_0(X6)
        | v2_struct_0(X7)
        | r1_tsep_1(X6,sK2)
        | ~ m1_pre_topc(X7,sK0) )
    | ~ spl5_142 ),
    inference(avatar_component_clause,[],[f827])).

fof(f829,plain,
    ( spl5_142
    | spl5_10
    | ~ spl5_9
    | ~ spl5_16
    | ~ spl5_60 ),
    inference(avatar_split_clause,[],[f815,f359,f123,f89,f93,f827])).

fof(f123,plain,
    ( spl5_16
  <=> ! [X1,X0] :
        ( r1_tsep_1(X0,X1)
        | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f359,plain,
    ( spl5_60
  <=> ! [X1,X0,X2] :
        ( ~ r1_tsep_1(X0,X1)
        | r1_tsep_1(X0,X2)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f815,plain,
    ( ! [X6,X7] :
        ( v2_struct_0(sK2)
        | r1_tsep_1(X6,sK2)
        | v2_struct_0(X7)
        | ~ m1_pre_topc(X7,sK0)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0)
        | ~ m1_pre_topc(sK2,X7)
        | k3_xboole_0(u1_struct_0(X6),u1_struct_0(X7)) = u1_struct_0(k2_tsep_1(sK0,X6,X7)) )
    | ~ spl5_9
    | ~ spl5_16
    | ~ spl5_60 ),
    inference(resolution,[],[f371,f90])).

fof(f90,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f89])).

fof(f371,plain,
    ( ! [X6,X4,X5] :
        ( ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X5)
        | r1_tsep_1(X4,X5)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK0)
        | ~ m1_pre_topc(X5,X6)
        | k3_xboole_0(u1_struct_0(X4),u1_struct_0(X6)) = u1_struct_0(k2_tsep_1(sK0,X4,X6)) )
    | ~ spl5_16
    | ~ spl5_60 ),
    inference(duplicate_literal_removal,[],[f368])).

fof(f368,plain,
    ( ! [X6,X4,X5] :
        ( r1_tsep_1(X4,X5)
        | v2_struct_0(X5)
        | ~ m1_pre_topc(X5,sK0)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0)
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK0)
        | ~ m1_pre_topc(X5,X6)
        | k3_xboole_0(u1_struct_0(X4),u1_struct_0(X6)) = u1_struct_0(k2_tsep_1(sK0,X4,X6))
        | v2_struct_0(X4)
        | ~ m1_pre_topc(X4,sK0)
        | v2_struct_0(X6)
        | ~ m1_pre_topc(X6,sK0) )
    | ~ spl5_16
    | ~ spl5_60 ),
    inference(resolution,[],[f360,f124])).

fof(f124,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(X0,X1)
        | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1))
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0) )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f123])).

fof(f360,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tsep_1(X0,X1)
        | r1_tsep_1(X0,X2)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | ~ m1_pre_topc(X2,X1) )
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f359])).

fof(f361,plain,
    ( spl5_15
    | ~ spl5_13
    | spl5_60
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f357,f109,f359,f105,f113])).

fof(f357,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X2,X1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK0)
        | r1_tsep_1(X0,X2)
        | v2_struct_0(sK0) )
    | ~ spl5_14 ),
    inference(resolution,[],[f46,f110])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tsep_1(X3,X2)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | r1_tsep_1(X3,X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( r1_tsep_1(X3,X1)
                    & r1_tsep_1(X1,X3) )
                  | ( ~ r1_tsep_1(X3,X2)
                    & ~ r1_tsep_1(X2,X3) )
                  | ~ m1_pre_topc(X1,X2)
                  | ~ m1_pre_topc(X3,X0)
                  | v2_struct_0(X3) )
              | ~ m1_pre_topc(X2,X0)
              | v2_struct_0(X2) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
                 => ( m1_pre_topc(X1,X2)
                   => ( ( r1_tsep_1(X3,X1)
                        & r1_tsep_1(X1,X3) )
                      | ( ~ r1_tsep_1(X3,X2)
                        & ~ r1_tsep_1(X2,X3) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).

fof(f168,plain,
    ( ~ spl5_9
    | spl5_10
    | ~ spl5_11
    | spl5_12
    | spl5_24
    | spl5_2
    | ~ spl5_18 ),
    inference(avatar_split_clause,[],[f164,f138,f61,f166,f101,f97,f93,f89])).

fof(f61,plain,
    ( spl5_2
  <=> r1_tsep_1(sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f138,plain,
    ( spl5_18
  <=> ! [X1,X0,X2] :
        ( ~ r1_tsep_1(X0,X1)
        | r1_tsep_1(X2,X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ r1_tsep_1(X0,sK2)
        | v2_struct_0(sK1)
        | ~ m1_pre_topc(sK1,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(sK2)
        | ~ m1_pre_topc(sK2,sK0)
        | ~ m1_pre_topc(sK1,X0) )
    | spl5_2
    | ~ spl5_18 ),
    inference(resolution,[],[f139,f62])).

fof(f62,plain,
    ( ~ r1_tsep_1(sK1,sK2)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f61])).

fof(f139,plain,
    ( ! [X2,X0,X1] :
        ( r1_tsep_1(X2,X1)
        | ~ r1_tsep_1(X0,X1)
        | v2_struct_0(X2)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | ~ m1_pre_topc(X2,X0) )
    | ~ spl5_18 ),
    inference(avatar_component_clause,[],[f138])).

fof(f140,plain,
    ( spl5_15
    | ~ spl5_13
    | spl5_18
    | ~ spl5_14 ),
    inference(avatar_split_clause,[],[f135,f109,f138,f105,f113])).

fof(f135,plain,
    ( ! [X2,X0,X1] :
        ( ~ r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X2,X0)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X2,sK0)
        | v2_struct_0(X2)
        | ~ l1_pre_topc(sK0)
        | r1_tsep_1(X2,X1)
        | v2_struct_0(sK0) )
    | ~ spl5_14 ),
    inference(resolution,[],[f43,f110])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ r1_tsep_1(X2,X3)
      | ~ m1_pre_topc(X1,X2)
      | ~ m1_pre_topc(X3,X0)
      | v2_struct_0(X3)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | r1_tsep_1(X1,X3)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f134,plain,
    ( ~ spl5_9
    | spl5_10
    | ~ spl5_11
    | spl5_12
    | spl5_17
    | spl5_2
    | ~ spl5_16 ),
    inference(avatar_split_clause,[],[f126,f123,f61,f132,f101,f97,f93,f89])).

fof(f126,plain,
    ( k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | spl5_2
    | ~ spl5_16 ),
    inference(resolution,[],[f124,f62])).

fof(f125,plain,
    ( spl5_15
    | spl5_16
    | ~ spl5_13 ),
    inference(avatar_split_clause,[],[f120,f105,f123,f113])).

fof(f120,plain,
    ( ! [X0,X1] :
        ( r1_tsep_1(X0,X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1))
        | v2_struct_0(sK0) )
    | ~ spl5_13 ),
    inference(resolution,[],[f118,f106])).

fof(f106,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_13 ),
    inference(avatar_component_clause,[],[f105])).

fof(f118,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f117,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f117,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f116,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2))
      | ~ v1_pre_topc(k2_tsep_1(X0,X1,X2))
      | v2_struct_0(k2_tsep_1(X0,X1,X2))
      | r1_tsep_1(X1,X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f55,f53])).

fof(f55,plain,(
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
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
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
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(nnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f115,plain,(
    ~ spl5_15 ),
    inference(avatar_split_clause,[],[f28,f113])).

fof(f28,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,
    ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK4))
    & ~ r1_tsep_1(sK1,sK2)
    & m1_pre_topc(sK2,sK4)
    & m1_pre_topc(sK1,sK3)
    & m1_pre_topc(sK4,sK0)
    & ~ v2_struct_0(sK4)
    & m1_pre_topc(sK3,sK0)
    & ~ v2_struct_0(sK3)
    & m1_pre_topc(sK2,sK0)
    & ~ v2_struct_0(sK2)
    & m1_pre_topc(sK1,sK0)
    & ~ v2_struct_0(sK1)
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0)
    & ~ v2_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f24,f23,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                        & ~ r1_tsep_1(X1,X2)
                        & m1_pre_topc(X2,X4)
                        & m1_pre_topc(X1,X3)
                        & m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
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
                  ( ? [X4] :
                      ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),k2_tsep_1(sK0,X3,X4))
                      & ~ r1_tsep_1(X1,X2)
                      & m1_pre_topc(X2,X4)
                      & m1_pre_topc(X1,X3)
                      & m1_pre_topc(X4,sK0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,sK0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,sK0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,sK0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0)
      & ~ v2_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ~ m1_pre_topc(k2_tsep_1(sK0,X1,X2),k2_tsep_1(sK0,X3,X4))
                    & ~ r1_tsep_1(X1,X2)
                    & m1_pre_topc(X2,X4)
                    & m1_pre_topc(X1,X3)
                    & m1_pre_topc(X4,sK0)
                    & ~ v2_struct_0(X4) )
                & m1_pre_topc(X3,sK0)
                & ~ v2_struct_0(X3) )
            & m1_pre_topc(X2,sK0)
            & ~ v2_struct_0(X2) )
        & m1_pre_topc(X1,sK0)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X2),k2_tsep_1(sK0,X3,X4))
                  & ~ r1_tsep_1(sK1,X2)
                  & m1_pre_topc(X2,X4)
                  & m1_pre_topc(sK1,X3)
                  & m1_pre_topc(X4,sK0)
                  & ~ v2_struct_0(X4) )
              & m1_pre_topc(X3,sK0)
              & ~ v2_struct_0(X3) )
          & m1_pre_topc(X2,sK0)
          & ~ v2_struct_0(X2) )
      & m1_pre_topc(sK1,sK0)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,X2),k2_tsep_1(sK0,X3,X4))
                & ~ r1_tsep_1(sK1,X2)
                & m1_pre_topc(X2,X4)
                & m1_pre_topc(sK1,X3)
                & m1_pre_topc(X4,sK0)
                & ~ v2_struct_0(X4) )
            & m1_pre_topc(X3,sK0)
            & ~ v2_struct_0(X3) )
        & m1_pre_topc(X2,sK0)
        & ~ v2_struct_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,X3,X4))
              & ~ r1_tsep_1(sK1,sK2)
              & m1_pre_topc(sK2,X4)
              & m1_pre_topc(sK1,X3)
              & m1_pre_topc(X4,sK0)
              & ~ v2_struct_0(X4) )
          & m1_pre_topc(X3,sK0)
          & ~ v2_struct_0(X3) )
      & m1_pre_topc(sK2,sK0)
      & ~ v2_struct_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f23,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,X3,X4))
            & ~ r1_tsep_1(sK1,sK2)
            & m1_pre_topc(sK2,X4)
            & m1_pre_topc(sK1,X3)
            & m1_pre_topc(X4,sK0)
            & ~ v2_struct_0(X4) )
        & m1_pre_topc(X3,sK0)
        & ~ v2_struct_0(X3) )
   => ( ? [X4] :
          ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,X4))
          & ~ r1_tsep_1(sK1,sK2)
          & m1_pre_topc(sK2,X4)
          & m1_pre_topc(sK1,sK3)
          & m1_pre_topc(X4,sK0)
          & ~ v2_struct_0(X4) )
      & m1_pre_topc(sK3,sK0)
      & ~ v2_struct_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f24,plain,
    ( ? [X4] :
        ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,X4))
        & ~ r1_tsep_1(sK1,sK2)
        & m1_pre_topc(sK2,X4)
        & m1_pre_topc(sK1,sK3)
        & m1_pre_topc(X4,sK0)
        & ~ v2_struct_0(X4) )
   => ( ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK4))
      & ~ r1_tsep_1(sK1,sK2)
      & m1_pre_topc(sK2,sK4)
      & m1_pre_topc(sK1,sK3)
      & m1_pre_topc(sK4,sK0)
      & ~ v2_struct_0(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f9,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      & ~ r1_tsep_1(X1,X2)
                      & m1_pre_topc(X2,X4)
                      & m1_pre_topc(X1,X3)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f8])).

fof(f8,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ~ m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                      & ~ r1_tsep_1(X1,X2)
                      & m1_pre_topc(X2,X4)
                      & m1_pre_topc(X1,X3)
                      & m1_pre_topc(X4,X0)
                      & ~ v2_struct_0(X4) )
                  & m1_pre_topc(X3,X0)
                  & ~ v2_struct_0(X3) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
                   => ! [X4] :
                        ( ( m1_pre_topc(X4,X0)
                          & ~ v2_struct_0(X4) )
                       => ( ( m1_pre_topc(X2,X4)
                            & m1_pre_topc(X1,X3) )
                         => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                            | r1_tsep_1(X1,X2) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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
                 => ! [X4] :
                      ( ( m1_pre_topc(X4,X0)
                        & ~ v2_struct_0(X4) )
                     => ( ( m1_pre_topc(X2,X4)
                          & m1_pre_topc(X1,X3) )
                       => ( m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4))
                          | r1_tsep_1(X1,X2) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tmap_1)).

fof(f111,plain,(
    spl5_14 ),
    inference(avatar_split_clause,[],[f29,f109])).

fof(f29,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f107,plain,(
    spl5_13 ),
    inference(avatar_split_clause,[],[f30,f105])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f103,plain,(
    ~ spl5_12 ),
    inference(avatar_split_clause,[],[f31,f101])).

fof(f31,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f99,plain,(
    spl5_11 ),
    inference(avatar_split_clause,[],[f32,f97])).

fof(f32,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f95,plain,(
    ~ spl5_10 ),
    inference(avatar_split_clause,[],[f33,f93])).

fof(f33,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f91,plain,(
    spl5_9 ),
    inference(avatar_split_clause,[],[f34,f89])).

fof(f34,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f87,plain,(
    ~ spl5_8 ),
    inference(avatar_split_clause,[],[f35,f85])).

fof(f35,plain,(
    ~ v2_struct_0(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f83,plain,(
    spl5_7 ),
    inference(avatar_split_clause,[],[f36,f81])).

fof(f36,plain,(
    m1_pre_topc(sK3,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f79,plain,(
    ~ spl5_6 ),
    inference(avatar_split_clause,[],[f37,f77])).

fof(f37,plain,(
    ~ v2_struct_0(sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f75,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f38,f73])).

fof(f38,plain,(
    m1_pre_topc(sK4,sK0) ),
    inference(cnf_transformation,[],[f25])).

fof(f71,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f39,f69])).

fof(f39,plain,(
    m1_pre_topc(sK1,sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f67,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f40,f65])).

fof(f40,plain,(
    m1_pre_topc(sK2,sK4) ),
    inference(cnf_transformation,[],[f25])).

fof(f63,plain,(
    ~ spl5_2 ),
    inference(avatar_split_clause,[],[f41,f61])).

fof(f41,plain,(
    ~ r1_tsep_1(sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f59,plain,(
    ~ spl5_1 ),
    inference(avatar_split_clause,[],[f42,f57])).

fof(f42,plain,(
    ~ m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK4)) ),
    inference(cnf_transformation,[],[f25])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:10:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.22/0.46  % (23817)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.47  % (23834)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (23834)Refutation not found, incomplete strategy% (23834)------------------------------
% 0.22/0.48  % (23834)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.48  % (23834)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.48  
% 0.22/0.48  % (23834)Memory used [KB]: 10618
% 0.22/0.48  % (23834)Time elapsed: 0.066 s
% 0.22/0.48  % (23834)------------------------------
% 0.22/0.48  % (23834)------------------------------
% 0.22/0.48  % (23828)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.48  % (23826)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.48  % (23814)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.48  % (23821)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.49  % (23829)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.49  % (23816)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.49  % (23813)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.49  % (23830)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.50  % (23815)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.50  % (23824)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.50  % (23823)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.50  % (23831)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.50  % (23819)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.51  % (23820)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (23832)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.51  % (23818)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (23825)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (23833)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.52  % (23822)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 1.51/0.56  % (23819)Refutation found. Thanks to Tanya!
% 1.51/0.56  % SZS status Theorem for theBenchmark
% 1.51/0.56  % SZS output start Proof for theBenchmark
% 1.51/0.56  fof(f1051,plain,(
% 1.51/0.56    $false),
% 1.51/0.56    inference(avatar_sat_refutation,[],[f59,f63,f67,f71,f75,f79,f83,f87,f91,f95,f99,f103,f107,f111,f115,f125,f134,f140,f168,f361,f829,f873,f897,f977,f988,f1003,f1025,f1026,f1034,f1037,f1046,f1048,f1050])).
% 1.51/0.56  fof(f1050,plain,(
% 1.51/0.56    spl5_15 | ~spl5_13 | spl5_8 | ~spl5_7 | spl5_6 | ~spl5_5 | spl5_178),
% 1.51/0.56    inference(avatar_split_clause,[],[f1049,f1044,f73,f77,f81,f85,f105,f113])).
% 1.51/0.56  fof(f113,plain,(
% 1.51/0.56    spl5_15 <=> v2_struct_0(sK0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 1.51/0.56  fof(f105,plain,(
% 1.51/0.56    spl5_13 <=> l1_pre_topc(sK0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 1.51/0.56  fof(f85,plain,(
% 1.51/0.56    spl5_8 <=> v2_struct_0(sK3)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_8])])).
% 1.51/0.56  fof(f81,plain,(
% 1.51/0.56    spl5_7 <=> m1_pre_topc(sK3,sK0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_7])])).
% 1.51/0.56  fof(f77,plain,(
% 1.51/0.56    spl5_6 <=> v2_struct_0(sK4)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 1.51/0.56  fof(f73,plain,(
% 1.51/0.56    spl5_5 <=> m1_pre_topc(sK4,sK0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.51/0.56  fof(f1044,plain,(
% 1.51/0.56    spl5_178 <=> m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),sK0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_178])])).
% 1.51/0.56  fof(f1049,plain,(
% 1.51/0.56    ~m1_pre_topc(sK4,sK0) | v2_struct_0(sK4) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl5_178),
% 1.51/0.56    inference(resolution,[],[f1045,f53])).
% 1.51/0.56  fof(f53,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f17])).
% 1.51/0.56  fof(f17,plain,(
% 1.51/0.56    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.51/0.56    inference(flattening,[],[f16])).
% 1.51/0.56  fof(f16,plain,(
% 1.51/0.56    ! [X0,X1,X2] : ((m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f3])).
% 1.51/0.56  fof(f3,axiom,(
% 1.51/0.56    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k2_tsep_1(X0,X1,X2)) & ~v2_struct_0(k2_tsep_1(X0,X1,X2))))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tsep_1)).
% 1.51/0.56  fof(f1045,plain,(
% 1.51/0.56    ~m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),sK0) | spl5_178),
% 1.51/0.56    inference(avatar_component_clause,[],[f1044])).
% 1.51/0.56  fof(f1048,plain,(
% 1.51/0.56    spl5_15 | ~spl5_13 | spl5_12 | ~spl5_11 | spl5_10 | ~spl5_9 | spl5_177),
% 1.51/0.56    inference(avatar_split_clause,[],[f1047,f1041,f89,f93,f97,f101,f105,f113])).
% 1.51/0.56  fof(f101,plain,(
% 1.51/0.56    spl5_12 <=> v2_struct_0(sK1)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).
% 1.51/0.56  fof(f97,plain,(
% 1.51/0.56    spl5_11 <=> m1_pre_topc(sK1,sK0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_11])])).
% 1.51/0.56  fof(f93,plain,(
% 1.51/0.56    spl5_10 <=> v2_struct_0(sK2)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.51/0.56  fof(f89,plain,(
% 1.51/0.56    spl5_9 <=> m1_pre_topc(sK2,sK0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).
% 1.51/0.56  fof(f1041,plain,(
% 1.51/0.56    spl5_177 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_177])])).
% 1.51/0.56  fof(f1047,plain,(
% 1.51/0.56    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK1) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | spl5_177),
% 1.51/0.56    inference(resolution,[],[f1042,f53])).
% 1.51/0.56  fof(f1042,plain,(
% 1.51/0.56    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | spl5_177),
% 1.51/0.56    inference(avatar_component_clause,[],[f1041])).
% 1.51/0.56  fof(f1046,plain,(
% 1.51/0.56    ~spl5_177 | ~spl5_13 | ~spl5_178 | ~spl5_14 | ~spl5_175),
% 1.51/0.56    inference(avatar_split_clause,[],[f1039,f1022,f109,f1044,f105,f1041])).
% 1.51/0.56  fof(f109,plain,(
% 1.51/0.56    spl5_14 <=> v2_pre_topc(sK0)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 1.51/0.56  fof(f1022,plain,(
% 1.51/0.56    spl5_175 <=> ! [X0] : (~m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_175])])).
% 1.51/0.56  fof(f1039,plain,(
% 1.51/0.56    ~m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),sK0) | (~spl5_14 | ~spl5_175)),
% 1.51/0.56    inference(resolution,[],[f1023,f110])).
% 1.51/0.56  fof(f110,plain,(
% 1.51/0.56    v2_pre_topc(sK0) | ~spl5_14),
% 1.51/0.56    inference(avatar_component_clause,[],[f109])).
% 1.51/0.56  fof(f1023,plain,(
% 1.51/0.56    ( ! [X0] : (~v2_pre_topc(X0) | ~m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0)) ) | ~spl5_175),
% 1.51/0.56    inference(avatar_component_clause,[],[f1022])).
% 1.51/0.56  fof(f1037,plain,(
% 1.51/0.56    ~spl5_9 | ~spl5_13 | ~spl5_5 | ~spl5_14 | ~spl5_169),
% 1.51/0.56    inference(avatar_split_clause,[],[f1036,f985,f109,f73,f105,f89])).
% 1.51/0.56  fof(f985,plain,(
% 1.51/0.56    spl5_169 <=> ! [X0] : (~m1_pre_topc(sK4,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_169])])).
% 1.51/0.56  fof(f1036,plain,(
% 1.51/0.56    ~m1_pre_topc(sK4,sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2,sK0) | (~spl5_14 | ~spl5_169)),
% 1.51/0.56    inference(resolution,[],[f986,f110])).
% 1.51/0.56  fof(f986,plain,(
% 1.51/0.56    ( ! [X0] : (~v2_pre_topc(X0) | ~m1_pre_topc(sK4,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK2,X0)) ) | ~spl5_169),
% 1.51/0.56    inference(avatar_component_clause,[],[f985])).
% 1.51/0.56  fof(f1034,plain,(
% 1.51/0.56    ~spl5_11 | ~spl5_13 | ~spl5_7 | ~spl5_14 | ~spl5_167),
% 1.51/0.56    inference(avatar_split_clause,[],[f1033,f974,f109,f81,f105,f97])).
% 1.51/0.56  fof(f974,plain,(
% 1.51/0.56    spl5_167 <=> ! [X0] : (~m1_pre_topc(sK3,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_167])])).
% 1.51/0.56  fof(f1033,plain,(
% 1.51/0.56    ~m1_pre_topc(sK3,sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(sK1,sK0) | (~spl5_14 | ~spl5_167)),
% 1.51/0.56    inference(resolution,[],[f975,f110])).
% 1.51/0.56  fof(f975,plain,(
% 1.51/0.56    ( ! [X0] : (~v2_pre_topc(X0) | ~m1_pre_topc(sK3,X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(sK1,X0)) ) | ~spl5_167),
% 1.51/0.56    inference(avatar_component_clause,[],[f974])).
% 1.51/0.56  fof(f1026,plain,(
% 1.51/0.56    ~spl5_33 | ~spl5_164 | spl5_165 | ~spl5_17 | ~spl5_153),
% 1.51/0.56    inference(avatar_split_clause,[],[f1016,f892,f132,f965,f962,f218])).
% 1.51/0.56  fof(f218,plain,(
% 1.51/0.56    spl5_33 <=> r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_33])])).
% 1.51/0.56  fof(f962,plain,(
% 1.51/0.56    spl5_164 <=> r1_tarski(u1_struct_0(sK2),u1_struct_0(sK4))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_164])])).
% 1.51/0.56  fof(f965,plain,(
% 1.51/0.56    spl5_165 <=> r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4)))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_165])])).
% 1.51/0.56  fof(f132,plain,(
% 1.51/0.56    spl5_17 <=> k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_17])])).
% 1.51/0.56  fof(f892,plain,(
% 1.51/0.56    spl5_153 <=> k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k2_tsep_1(sK0,sK3,sK4))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_153])])).
% 1.51/0.56  fof(f1016,plain,(
% 1.51/0.56    r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4))) | ~r1_tarski(u1_struct_0(sK2),u1_struct_0(sK4)) | ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) | (~spl5_17 | ~spl5_153)),
% 1.51/0.56    inference(superposition,[],[f142,f893])).
% 1.51/0.56  fof(f893,plain,(
% 1.51/0.56    k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k2_tsep_1(sK0,sK3,sK4)) | ~spl5_153),
% 1.51/0.56    inference(avatar_component_clause,[],[f892])).
% 1.51/0.56  fof(f142,plain,(
% 1.51/0.56    ( ! [X2,X3] : (r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),k3_xboole_0(X2,X3)) | ~r1_tarski(u1_struct_0(sK2),X3) | ~r1_tarski(u1_struct_0(sK1),X2)) ) | ~spl5_17),
% 1.51/0.56    inference(superposition,[],[f54,f133])).
% 1.51/0.56  fof(f133,plain,(
% 1.51/0.56    k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | ~spl5_17),
% 1.51/0.56    inference(avatar_component_clause,[],[f132])).
% 1.51/0.56  fof(f54,plain,(
% 1.51/0.56    ( ! [X2,X0,X3,X1] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f19])).
% 1.51/0.56  fof(f19,plain,(
% 1.51/0.56    ! [X0,X1,X2,X3] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) | ~r1_tarski(X2,X3) | ~r1_tarski(X0,X1))),
% 1.51/0.56    inference(flattening,[],[f18])).
% 1.51/0.56  fof(f18,plain,(
% 1.51/0.56    ! [X0,X1,X2,X3] : (r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)) | (~r1_tarski(X2,X3) | ~r1_tarski(X0,X1)))),
% 1.51/0.56    inference(ennf_transformation,[],[f1])).
% 1.51/0.56  fof(f1,axiom,(
% 1.51/0.56    ! [X0,X1,X2,X3] : ((r1_tarski(X2,X3) & r1_tarski(X0,X1)) => r1_tarski(k3_xboole_0(X0,X2),k3_xboole_0(X1,X3)))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_xboole_1)).
% 1.51/0.56  fof(f1025,plain,(
% 1.51/0.56    spl5_175 | spl5_1 | ~spl5_165),
% 1.51/0.56    inference(avatar_split_clause,[],[f1020,f965,f57,f1022])).
% 1.51/0.56  fof(f57,plain,(
% 1.51/0.56    spl5_1 <=> m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK4))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.51/0.56  fof(f1020,plain,(
% 1.51/0.56    ( ! [X0] : (m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK4)) | ~m1_pre_topc(k2_tsep_1(sK0,sK3,sK4),X0) | ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | ~spl5_165),
% 1.51/0.56    inference(resolution,[],[f966,f49])).
% 1.51/0.56  fof(f49,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f27])).
% 1.51/0.56  fof(f27,plain,(
% 1.51/0.56    ! [X0] : (! [X1] : (! [X2] : (((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2)) & (m1_pre_topc(X1,X2) | ~r1_tarski(u1_struct_0(X1),u1_struct_0(X2)))) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.51/0.56    inference(nnf_transformation,[],[f15])).
% 1.51/0.56  fof(f15,plain,(
% 1.51/0.56    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.51/0.56    inference(flattening,[],[f14])).
% 1.51/0.56  fof(f14,plain,(
% 1.51/0.56    ! [X0] : (! [X1] : (! [X2] : ((r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)) | ~m1_pre_topc(X2,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f5])).
% 1.51/0.56  fof(f5,axiom,(
% 1.51/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_pre_topc(X2,X0) => (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) <=> m1_pre_topc(X1,X2)))))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_tsep_1)).
% 1.51/0.56  fof(f966,plain,(
% 1.51/0.56    r1_tarski(u1_struct_0(k2_tsep_1(sK0,sK1,sK2)),u1_struct_0(k2_tsep_1(sK0,sK3,sK4))) | ~spl5_165),
% 1.51/0.56    inference(avatar_component_clause,[],[f965])).
% 1.51/0.56  fof(f1003,plain,(
% 1.51/0.56    spl5_8 | ~spl5_7 | ~spl5_4 | ~spl5_24 | ~spl5_154),
% 1.51/0.56    inference(avatar_split_clause,[],[f991,f895,f166,f69,f81,f85])).
% 1.51/0.56  fof(f69,plain,(
% 1.51/0.56    spl5_4 <=> m1_pre_topc(sK1,sK3)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.51/0.56  fof(f166,plain,(
% 1.51/0.56    spl5_24 <=> ! [X0] : (~r1_tsep_1(X0,sK2) | ~m1_pre_topc(sK1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).
% 1.51/0.56  fof(f895,plain,(
% 1.51/0.56    spl5_154 <=> r1_tsep_1(sK3,sK2)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_154])])).
% 1.51/0.56  fof(f991,plain,(
% 1.51/0.56    ~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK3,sK0) | v2_struct_0(sK3) | (~spl5_24 | ~spl5_154)),
% 1.51/0.56    inference(resolution,[],[f896,f167])).
% 1.51/0.56  fof(f167,plain,(
% 1.51/0.56    ( ! [X0] : (~r1_tsep_1(X0,sK2) | ~m1_pre_topc(sK1,X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0)) ) | ~spl5_24),
% 1.51/0.56    inference(avatar_component_clause,[],[f166])).
% 1.51/0.56  fof(f896,plain,(
% 1.51/0.56    r1_tsep_1(sK3,sK2) | ~spl5_154),
% 1.51/0.56    inference(avatar_component_clause,[],[f895])).
% 1.51/0.56  fof(f988,plain,(
% 1.51/0.56    spl5_169 | ~spl5_3 | spl5_164),
% 1.51/0.56    inference(avatar_split_clause,[],[f983,f962,f65,f985])).
% 1.51/0.56  fof(f65,plain,(
% 1.51/0.56    spl5_3 <=> m1_pre_topc(sK2,sK4)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.51/0.56  fof(f983,plain,(
% 1.51/0.56    ( ! [X0] : (~m1_pre_topc(sK2,sK4) | ~m1_pre_topc(sK4,X0) | ~m1_pre_topc(sK2,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | spl5_164),
% 1.51/0.56    inference(resolution,[],[f963,f50])).
% 1.51/0.56  fof(f50,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X2)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f27])).
% 1.51/0.56  fof(f963,plain,(
% 1.51/0.56    ~r1_tarski(u1_struct_0(sK2),u1_struct_0(sK4)) | spl5_164),
% 1.51/0.56    inference(avatar_component_clause,[],[f962])).
% 1.51/0.56  fof(f977,plain,(
% 1.51/0.56    spl5_167 | ~spl5_4 | spl5_33),
% 1.51/0.56    inference(avatar_split_clause,[],[f972,f218,f69,f974])).
% 1.51/0.56  fof(f972,plain,(
% 1.51/0.56    ( ! [X0] : (~m1_pre_topc(sK1,sK3) | ~m1_pre_topc(sK3,X0) | ~m1_pre_topc(sK1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) ) | spl5_33),
% 1.51/0.56    inference(resolution,[],[f219,f50])).
% 1.51/0.56  fof(f219,plain,(
% 1.51/0.56    ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK3)) | spl5_33),
% 1.51/0.56    inference(avatar_component_clause,[],[f218])).
% 1.51/0.56  fof(f897,plain,(
% 1.51/0.56    spl5_153 | spl5_8 | spl5_154 | ~spl5_7 | ~spl5_149),
% 1.51/0.56    inference(avatar_split_clause,[],[f877,f871,f81,f895,f85,f892])).
% 1.51/0.56  fof(f871,plain,(
% 1.51/0.56    spl5_149 <=> ! [X0] : (k3_xboole_0(u1_struct_0(X0),u1_struct_0(sK4)) = u1_struct_0(k2_tsep_1(sK0,X0,sK4)) | r1_tsep_1(X0,sK2) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_149])])).
% 1.51/0.56  fof(f877,plain,(
% 1.51/0.56    r1_tsep_1(sK3,sK2) | v2_struct_0(sK3) | k3_xboole_0(u1_struct_0(sK3),u1_struct_0(sK4)) = u1_struct_0(k2_tsep_1(sK0,sK3,sK4)) | (~spl5_7 | ~spl5_149)),
% 1.51/0.56    inference(resolution,[],[f872,f82])).
% 1.51/0.56  fof(f82,plain,(
% 1.51/0.56    m1_pre_topc(sK3,sK0) | ~spl5_7),
% 1.51/0.56    inference(avatar_component_clause,[],[f81])).
% 1.51/0.56  fof(f872,plain,(
% 1.51/0.56    ( ! [X0] : (~m1_pre_topc(X0,sK0) | r1_tsep_1(X0,sK2) | v2_struct_0(X0) | k3_xboole_0(u1_struct_0(X0),u1_struct_0(sK4)) = u1_struct_0(k2_tsep_1(sK0,X0,sK4))) ) | ~spl5_149),
% 1.51/0.56    inference(avatar_component_clause,[],[f871])).
% 1.51/0.56  fof(f873,plain,(
% 1.51/0.56    ~spl5_5 | spl5_6 | spl5_149 | ~spl5_3 | ~spl5_142),
% 1.51/0.56    inference(avatar_split_clause,[],[f868,f827,f65,f871,f77,f73])).
% 1.51/0.56  fof(f827,plain,(
% 1.51/0.56    spl5_142 <=> ! [X7,X6] : (r1_tsep_1(X6,sK2) | k3_xboole_0(u1_struct_0(X6),u1_struct_0(X7)) = u1_struct_0(k2_tsep_1(sK0,X6,X7)) | ~m1_pre_topc(X6,sK0) | v2_struct_0(X6) | v2_struct_0(X7) | ~m1_pre_topc(sK2,X7) | ~m1_pre_topc(X7,sK0))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_142])])).
% 1.51/0.56  fof(f868,plain,(
% 1.51/0.56    ( ! [X0] : (k3_xboole_0(u1_struct_0(X0),u1_struct_0(sK4)) = u1_struct_0(k2_tsep_1(sK0,X0,sK4)) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v2_struct_0(sK4) | r1_tsep_1(X0,sK2) | ~m1_pre_topc(sK4,sK0)) ) | (~spl5_3 | ~spl5_142)),
% 1.51/0.56    inference(resolution,[],[f828,f66])).
% 1.51/0.56  fof(f66,plain,(
% 1.51/0.56    m1_pre_topc(sK2,sK4) | ~spl5_3),
% 1.51/0.56    inference(avatar_component_clause,[],[f65])).
% 1.51/0.56  fof(f828,plain,(
% 1.51/0.56    ( ! [X6,X7] : (~m1_pre_topc(sK2,X7) | k3_xboole_0(u1_struct_0(X6),u1_struct_0(X7)) = u1_struct_0(k2_tsep_1(sK0,X6,X7)) | ~m1_pre_topc(X6,sK0) | v2_struct_0(X6) | v2_struct_0(X7) | r1_tsep_1(X6,sK2) | ~m1_pre_topc(X7,sK0)) ) | ~spl5_142),
% 1.51/0.56    inference(avatar_component_clause,[],[f827])).
% 1.51/0.56  fof(f829,plain,(
% 1.51/0.56    spl5_142 | spl5_10 | ~spl5_9 | ~spl5_16 | ~spl5_60),
% 1.51/0.56    inference(avatar_split_clause,[],[f815,f359,f123,f89,f93,f827])).
% 1.51/0.56  fof(f123,plain,(
% 1.51/0.56    spl5_16 <=> ! [X1,X0] : (r1_tsep_1(X0,X1) | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1)) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 1.51/0.56  fof(f359,plain,(
% 1.51/0.56    spl5_60 <=> ! [X1,X0,X2] : (~r1_tsep_1(X0,X1) | r1_tsep_1(X0,X2) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X2,X1))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).
% 1.51/0.56  fof(f815,plain,(
% 1.51/0.56    ( ! [X6,X7] : (v2_struct_0(sK2) | r1_tsep_1(X6,sK2) | v2_struct_0(X7) | ~m1_pre_topc(X7,sK0) | v2_struct_0(X6) | ~m1_pre_topc(X6,sK0) | ~m1_pre_topc(sK2,X7) | k3_xboole_0(u1_struct_0(X6),u1_struct_0(X7)) = u1_struct_0(k2_tsep_1(sK0,X6,X7))) ) | (~spl5_9 | ~spl5_16 | ~spl5_60)),
% 1.51/0.56    inference(resolution,[],[f371,f90])).
% 1.51/0.56  fof(f90,plain,(
% 1.51/0.56    m1_pre_topc(sK2,sK0) | ~spl5_9),
% 1.51/0.56    inference(avatar_component_clause,[],[f89])).
% 1.51/0.56  fof(f371,plain,(
% 1.51/0.56    ( ! [X6,X4,X5] : (~m1_pre_topc(X5,sK0) | v2_struct_0(X5) | r1_tsep_1(X4,X5) | v2_struct_0(X6) | ~m1_pre_topc(X6,sK0) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK0) | ~m1_pre_topc(X5,X6) | k3_xboole_0(u1_struct_0(X4),u1_struct_0(X6)) = u1_struct_0(k2_tsep_1(sK0,X4,X6))) ) | (~spl5_16 | ~spl5_60)),
% 1.51/0.56    inference(duplicate_literal_removal,[],[f368])).
% 1.51/0.56  fof(f368,plain,(
% 1.51/0.56    ( ! [X6,X4,X5] : (r1_tsep_1(X4,X5) | v2_struct_0(X5) | ~m1_pre_topc(X5,sK0) | v2_struct_0(X6) | ~m1_pre_topc(X6,sK0) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK0) | ~m1_pre_topc(X5,X6) | k3_xboole_0(u1_struct_0(X4),u1_struct_0(X6)) = u1_struct_0(k2_tsep_1(sK0,X4,X6)) | v2_struct_0(X4) | ~m1_pre_topc(X4,sK0) | v2_struct_0(X6) | ~m1_pre_topc(X6,sK0)) ) | (~spl5_16 | ~spl5_60)),
% 1.51/0.56    inference(resolution,[],[f360,f124])).
% 1.51/0.56  fof(f124,plain,(
% 1.51/0.56    ( ! [X0,X1] : (r1_tsep_1(X0,X1) | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1)) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0)) ) | ~spl5_16),
% 1.51/0.56    inference(avatar_component_clause,[],[f123])).
% 1.51/0.56  fof(f360,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~r1_tsep_1(X0,X1) | r1_tsep_1(X0,X2) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | ~m1_pre_topc(X2,X1)) ) | ~spl5_60),
% 1.51/0.56    inference(avatar_component_clause,[],[f359])).
% 1.51/0.56  fof(f361,plain,(
% 1.51/0.56    spl5_15 | ~spl5_13 | spl5_60 | ~spl5_14),
% 1.51/0.56    inference(avatar_split_clause,[],[f357,f109,f359,f105,f113])).
% 1.51/0.56  fof(f357,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~r1_tsep_1(X0,X1) | ~m1_pre_topc(X2,X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | r1_tsep_1(X0,X2) | v2_struct_0(sK0)) ) | ~spl5_14),
% 1.51/0.56    inference(resolution,[],[f46,f110])).
% 1.51/0.56  fof(f46,plain,(
% 1.51/0.56    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~r1_tsep_1(X3,X2) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | r1_tsep_1(X3,X1) | v2_struct_0(X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f11])).
% 1.51/0.56  fof(f11,plain,(
% 1.51/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3)) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.51/0.56    inference(flattening,[],[f10])).
% 1.51/0.56  fof(f10,plain,(
% 1.51/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))) | ~m1_pre_topc(X1,X2)) | (~m1_pre_topc(X3,X0) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f4])).
% 1.51/0.56  fof(f4,axiom,(
% 1.51/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => (m1_pre_topc(X1,X2) => ((r1_tsep_1(X3,X1) & r1_tsep_1(X1,X3)) | (~r1_tsep_1(X3,X2) & ~r1_tsep_1(X2,X3))))))))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_tmap_1)).
% 1.51/0.56  fof(f168,plain,(
% 1.51/0.56    ~spl5_9 | spl5_10 | ~spl5_11 | spl5_12 | spl5_24 | spl5_2 | ~spl5_18),
% 1.51/0.56    inference(avatar_split_clause,[],[f164,f138,f61,f166,f101,f97,f93,f89])).
% 1.51/0.56  fof(f61,plain,(
% 1.51/0.56    spl5_2 <=> r1_tsep_1(sK1,sK2)),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.51/0.56  fof(f138,plain,(
% 1.51/0.56    spl5_18 <=> ! [X1,X0,X2] : (~r1_tsep_1(X0,X1) | r1_tsep_1(X2,X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X2,X0))),
% 1.51/0.56    introduced(avatar_definition,[new_symbols(naming,[spl5_18])])).
% 1.51/0.56  fof(f164,plain,(
% 1.51/0.56    ( ! [X0] : (~r1_tsep_1(X0,sK2) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | ~m1_pre_topc(sK1,X0)) ) | (spl5_2 | ~spl5_18)),
% 1.51/0.56    inference(resolution,[],[f139,f62])).
% 1.51/0.56  fof(f62,plain,(
% 1.51/0.56    ~r1_tsep_1(sK1,sK2) | spl5_2),
% 1.51/0.56    inference(avatar_component_clause,[],[f61])).
% 1.51/0.56  fof(f139,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (r1_tsep_1(X2,X1) | ~r1_tsep_1(X0,X1) | v2_struct_0(X2) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | ~m1_pre_topc(X2,X0)) ) | ~spl5_18),
% 1.51/0.56    inference(avatar_component_clause,[],[f138])).
% 1.51/0.56  fof(f140,plain,(
% 1.51/0.56    spl5_15 | ~spl5_13 | spl5_18 | ~spl5_14),
% 1.51/0.56    inference(avatar_split_clause,[],[f135,f109,f138,f105,f113])).
% 1.51/0.56  fof(f135,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~r1_tsep_1(X0,X1) | ~m1_pre_topc(X2,X0) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | ~m1_pre_topc(X2,sK0) | v2_struct_0(X2) | ~l1_pre_topc(sK0) | r1_tsep_1(X2,X1) | v2_struct_0(sK0)) ) | ~spl5_14),
% 1.51/0.56    inference(resolution,[],[f43,f110])).
% 1.51/0.56  fof(f43,plain,(
% 1.51/0.56    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~r1_tsep_1(X2,X3) | ~m1_pre_topc(X1,X2) | ~m1_pre_topc(X3,X0) | v2_struct_0(X3) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | r1_tsep_1(X1,X3) | v2_struct_0(X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f11])).
% 1.51/0.56  fof(f134,plain,(
% 1.51/0.56    ~spl5_9 | spl5_10 | ~spl5_11 | spl5_12 | spl5_17 | spl5_2 | ~spl5_16),
% 1.51/0.56    inference(avatar_split_clause,[],[f126,f123,f61,f132,f101,f97,f93,f89])).
% 1.51/0.56  fof(f126,plain,(
% 1.51/0.56    k3_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) = u1_struct_0(k2_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | (spl5_2 | ~spl5_16)),
% 1.51/0.56    inference(resolution,[],[f124,f62])).
% 1.51/0.56  fof(f125,plain,(
% 1.51/0.56    spl5_15 | spl5_16 | ~spl5_13),
% 1.51/0.56    inference(avatar_split_clause,[],[f120,f105,f123,f113])).
% 1.51/0.56  fof(f120,plain,(
% 1.51/0.56    ( ! [X0,X1] : (r1_tsep_1(X0,X1) | ~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | ~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | k3_xboole_0(u1_struct_0(X0),u1_struct_0(X1)) = u1_struct_0(k2_tsep_1(sK0,X0,X1)) | v2_struct_0(sK0)) ) | ~spl5_13),
% 1.51/0.56    inference(resolution,[],[f118,f106])).
% 1.51/0.56  fof(f106,plain,(
% 1.51/0.56    l1_pre_topc(sK0) | ~spl5_13),
% 1.51/0.56    inference(avatar_component_clause,[],[f105])).
% 1.51/0.56  fof(f118,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | v2_struct_0(X0)) )),
% 1.51/0.56    inference(subsumption_resolution,[],[f117,f51])).
% 1.51/0.56  fof(f51,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (~v2_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f17])).
% 1.51/0.56  fof(f117,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.51/0.56    inference(subsumption_resolution,[],[f116,f52])).
% 1.51/0.56  fof(f52,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (v1_pre_topc(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f17])).
% 1.51/0.56  fof(f116,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.51/0.56    inference(subsumption_resolution,[],[f55,f53])).
% 1.51/0.56  fof(f55,plain,(
% 1.51/0.56    ( ! [X2,X0,X1] : (k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k2_tsep_1(X0,X1,X2)) | ~m1_pre_topc(k2_tsep_1(X0,X1,X2),X0) | ~v1_pre_topc(k2_tsep_1(X0,X1,X2)) | v2_struct_0(k2_tsep_1(X0,X1,X2)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.51/0.56    inference(equality_resolution,[],[f47])).
% 1.51/0.56  fof(f47,plain,(
% 1.51/0.56    ( ! [X2,X0,X3,X1] : (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3 | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)) )),
% 1.51/0.56    inference(cnf_transformation,[],[f26])).
% 1.51/0.56  fof(f26,plain,(
% 1.51/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((k2_tsep_1(X0,X1,X2) = X3 | u1_struct_0(X3) != k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) & (u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k2_tsep_1(X0,X1,X2) != X3)) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.51/0.56    inference(nnf_transformation,[],[f13])).
% 1.51/0.56  fof(f13,plain,(
% 1.51/0.56    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | r1_tsep_1(X1,X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.51/0.56    inference(flattening,[],[f12])).
% 1.51/0.56  fof(f12,plain,(
% 1.51/0.56    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | r1_tsep_1(X1,X2)) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f2])).
% 1.51/0.56  fof(f2,axiom,(
% 1.51/0.56    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => (~r1_tsep_1(X1,X2) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k2_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k3_xboole_0(u1_struct_0(X1),u1_struct_0(X2))))))))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tsep_1)).
% 1.51/0.56  fof(f115,plain,(
% 1.51/0.56    ~spl5_15),
% 1.51/0.56    inference(avatar_split_clause,[],[f28,f113])).
% 1.51/0.56  fof(f28,plain,(
% 1.51/0.56    ~v2_struct_0(sK0)),
% 1.51/0.56    inference(cnf_transformation,[],[f25])).
% 1.51/0.56  fof(f25,plain,(
% 1.51/0.56    ((((~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK4)) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK4) & m1_pre_topc(sK1,sK3) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0)),
% 1.51/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4])],[f9,f24,f23,f22,f21,f20])).
% 1.51/0.56  fof(f20,plain,(
% 1.51/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X4) & m1_pre_topc(X1,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~m1_pre_topc(k2_tsep_1(sK0,X1,X2),k2_tsep_1(sK0,X3,X4)) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X4) & m1_pre_topc(X1,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) & l1_pre_topc(sK0) & v2_pre_topc(sK0) & ~v2_struct_0(sK0))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f21,plain,(
% 1.51/0.56    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (~m1_pre_topc(k2_tsep_1(sK0,X1,X2),k2_tsep_1(sK0,X3,X4)) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X4) & m1_pre_topc(X1,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,sK0) & ~v2_struct_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,X2),k2_tsep_1(sK0,X3,X4)) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X2,X4) & m1_pre_topc(sK1,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) & m1_pre_topc(sK1,sK0) & ~v2_struct_0(sK1))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f22,plain,(
% 1.51/0.56    ? [X2] : (? [X3] : (? [X4] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,X2),k2_tsep_1(sK0,X3,X4)) & ~r1_tsep_1(sK1,X2) & m1_pre_topc(X2,X4) & m1_pre_topc(sK1,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,sK0) & ~v2_struct_0(X2)) => (? [X3] : (? [X4] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,X3,X4)) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,X4) & m1_pre_topc(sK1,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) & m1_pre_topc(sK2,sK0) & ~v2_struct_0(sK2))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f23,plain,(
% 1.51/0.56    ? [X3] : (? [X4] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,X3,X4)) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,X4) & m1_pre_topc(sK1,X3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,sK0) & ~v2_struct_0(X3)) => (? [X4] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,X4)) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,X4) & m1_pre_topc(sK1,sK3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) & m1_pre_topc(sK3,sK0) & ~v2_struct_0(sK3))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f24,plain,(
% 1.51/0.56    ? [X4] : (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,X4)) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,X4) & m1_pre_topc(sK1,sK3) & m1_pre_topc(X4,sK0) & ~v2_struct_0(X4)) => (~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK4)) & ~r1_tsep_1(sK1,sK2) & m1_pre_topc(sK2,sK4) & m1_pre_topc(sK1,sK3) & m1_pre_topc(sK4,sK0) & ~v2_struct_0(sK4))),
% 1.51/0.56    introduced(choice_axiom,[])).
% 1.51/0.56  fof(f9,plain,(
% 1.51/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (~m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) & ~r1_tsep_1(X1,X2) & m1_pre_topc(X2,X4) & m1_pre_topc(X1,X3) & m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) & m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.51/0.56    inference(flattening,[],[f8])).
% 1.51/0.56  fof(f8,plain,(
% 1.51/0.56    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (((~m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) & ~r1_tsep_1(X1,X2)) & (m1_pre_topc(X2,X4) & m1_pre_topc(X1,X3))) & (m1_pre_topc(X4,X0) & ~v2_struct_0(X4))) & (m1_pre_topc(X3,X0) & ~v2_struct_0(X3))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.51/0.56    inference(ennf_transformation,[],[f7])).
% 1.51/0.56  fof(f7,negated_conjecture,(
% 1.51/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X2,X4) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2))))))))),
% 1.51/0.56    inference(negated_conjecture,[],[f6])).
% 1.51/0.56  fof(f6,conjecture,(
% 1.51/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & ~v2_struct_0(X3)) => ! [X4] : ((m1_pre_topc(X4,X0) & ~v2_struct_0(X4)) => ((m1_pre_topc(X2,X4) & m1_pre_topc(X1,X3)) => (m1_pre_topc(k2_tsep_1(X0,X1,X2),k2_tsep_1(X0,X3,X4)) | r1_tsep_1(X1,X2))))))))),
% 1.51/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_tmap_1)).
% 1.51/0.56  fof(f111,plain,(
% 1.51/0.56    spl5_14),
% 1.51/0.56    inference(avatar_split_clause,[],[f29,f109])).
% 1.51/0.56  fof(f29,plain,(
% 1.51/0.56    v2_pre_topc(sK0)),
% 1.51/0.56    inference(cnf_transformation,[],[f25])).
% 1.51/0.56  fof(f107,plain,(
% 1.51/0.56    spl5_13),
% 1.51/0.56    inference(avatar_split_clause,[],[f30,f105])).
% 1.51/0.56  fof(f30,plain,(
% 1.51/0.56    l1_pre_topc(sK0)),
% 1.51/0.56    inference(cnf_transformation,[],[f25])).
% 1.51/0.56  fof(f103,plain,(
% 1.51/0.56    ~spl5_12),
% 1.51/0.56    inference(avatar_split_clause,[],[f31,f101])).
% 1.51/0.56  fof(f31,plain,(
% 1.51/0.56    ~v2_struct_0(sK1)),
% 1.51/0.56    inference(cnf_transformation,[],[f25])).
% 1.51/0.56  fof(f99,plain,(
% 1.51/0.56    spl5_11),
% 1.51/0.56    inference(avatar_split_clause,[],[f32,f97])).
% 1.51/0.56  fof(f32,plain,(
% 1.51/0.56    m1_pre_topc(sK1,sK0)),
% 1.51/0.56    inference(cnf_transformation,[],[f25])).
% 1.51/0.56  fof(f95,plain,(
% 1.51/0.56    ~spl5_10),
% 1.51/0.56    inference(avatar_split_clause,[],[f33,f93])).
% 1.51/0.56  fof(f33,plain,(
% 1.51/0.56    ~v2_struct_0(sK2)),
% 1.51/0.56    inference(cnf_transformation,[],[f25])).
% 1.51/0.56  fof(f91,plain,(
% 1.51/0.56    spl5_9),
% 1.51/0.56    inference(avatar_split_clause,[],[f34,f89])).
% 1.51/0.56  fof(f34,plain,(
% 1.51/0.56    m1_pre_topc(sK2,sK0)),
% 1.51/0.56    inference(cnf_transformation,[],[f25])).
% 1.51/0.56  fof(f87,plain,(
% 1.51/0.56    ~spl5_8),
% 1.51/0.56    inference(avatar_split_clause,[],[f35,f85])).
% 1.51/0.56  fof(f35,plain,(
% 1.51/0.56    ~v2_struct_0(sK3)),
% 1.51/0.56    inference(cnf_transformation,[],[f25])).
% 1.51/0.56  fof(f83,plain,(
% 1.51/0.56    spl5_7),
% 1.51/0.56    inference(avatar_split_clause,[],[f36,f81])).
% 1.51/0.56  fof(f36,plain,(
% 1.51/0.56    m1_pre_topc(sK3,sK0)),
% 1.51/0.56    inference(cnf_transformation,[],[f25])).
% 1.51/0.56  fof(f79,plain,(
% 1.51/0.56    ~spl5_6),
% 1.51/0.56    inference(avatar_split_clause,[],[f37,f77])).
% 1.51/0.56  fof(f37,plain,(
% 1.51/0.56    ~v2_struct_0(sK4)),
% 1.51/0.56    inference(cnf_transformation,[],[f25])).
% 1.51/0.56  fof(f75,plain,(
% 1.51/0.56    spl5_5),
% 1.51/0.56    inference(avatar_split_clause,[],[f38,f73])).
% 1.51/0.56  fof(f38,plain,(
% 1.51/0.56    m1_pre_topc(sK4,sK0)),
% 1.51/0.56    inference(cnf_transformation,[],[f25])).
% 1.51/0.56  fof(f71,plain,(
% 1.51/0.56    spl5_4),
% 1.51/0.56    inference(avatar_split_clause,[],[f39,f69])).
% 1.51/0.56  fof(f39,plain,(
% 1.51/0.56    m1_pre_topc(sK1,sK3)),
% 1.51/0.56    inference(cnf_transformation,[],[f25])).
% 1.51/0.56  fof(f67,plain,(
% 1.51/0.56    spl5_3),
% 1.51/0.56    inference(avatar_split_clause,[],[f40,f65])).
% 1.51/0.56  fof(f40,plain,(
% 1.51/0.56    m1_pre_topc(sK2,sK4)),
% 1.51/0.56    inference(cnf_transformation,[],[f25])).
% 1.51/0.56  fof(f63,plain,(
% 1.51/0.56    ~spl5_2),
% 1.51/0.56    inference(avatar_split_clause,[],[f41,f61])).
% 1.51/0.56  fof(f41,plain,(
% 1.51/0.56    ~r1_tsep_1(sK1,sK2)),
% 1.51/0.56    inference(cnf_transformation,[],[f25])).
% 1.51/0.56  fof(f59,plain,(
% 1.51/0.56    ~spl5_1),
% 1.51/0.56    inference(avatar_split_clause,[],[f42,f57])).
% 1.51/0.56  fof(f42,plain,(
% 1.51/0.56    ~m1_pre_topc(k2_tsep_1(sK0,sK1,sK2),k2_tsep_1(sK0,sK3,sK4))),
% 1.51/0.56    inference(cnf_transformation,[],[f25])).
% 1.51/0.56  % SZS output end Proof for theBenchmark
% 1.51/0.56  % (23819)------------------------------
% 1.51/0.56  % (23819)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.51/0.56  % (23819)Termination reason: Refutation
% 1.51/0.56  
% 1.51/0.56  % (23819)Memory used [KB]: 11513
% 1.51/0.56  % (23819)Time elapsed: 0.150 s
% 1.51/0.56  % (23819)------------------------------
% 1.51/0.56  % (23819)------------------------------
% 1.51/0.57  % (23809)Success in time 0.206 s
%------------------------------------------------------------------------------
