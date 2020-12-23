%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:47 EST 2020

% Result     : Theorem 2.31s
% Output     : Refutation 2.31s
% Verified   : 
% Statistics : Number of formulae       :  195 ( 434 expanded)
%              Number of leaves         :   37 ( 178 expanded)
%              Depth                    :   14
%              Number of atoms          :  923 (1979 expanded)
%              Number of equality atoms :   33 ( 126 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    4 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2658,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f74,f78,f82,f86,f90,f94,f98,f148,f156,f160,f210,f214,f228,f240,f256,f406,f410,f553,f997,f2160,f2170,f2566,f2624,f2638,f2647,f2657])).

fof(f2657,plain,
    ( spl7_11
    | ~ spl7_172 ),
    inference(avatar_contradiction_clause,[],[f2656])).

fof(f2656,plain,
    ( $false
    | spl7_11
    | ~ spl7_172 ),
    inference(subsumption_resolution,[],[f2653,f155])).

fof(f155,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK2))
    | spl7_11 ),
    inference(avatar_component_clause,[],[f154])).

fof(f154,plain,
    ( spl7_11
  <=> m1_subset_1(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).

fof(f2653,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK2))
    | ~ spl7_172 ),
    inference(resolution,[],[f2637,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f2637,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | ~ spl7_172 ),
    inference(avatar_component_clause,[],[f2636])).

fof(f2636,plain,
    ( spl7_172
  <=> r2_hidden(sK3,u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_172])])).

fof(f2647,plain,
    ( spl7_9
    | ~ spl7_171 ),
    inference(avatar_contradiction_clause,[],[f2646])).

fof(f2646,plain,
    ( $false
    | spl7_9
    | ~ spl7_171 ),
    inference(subsumption_resolution,[],[f2643,f147])).

fof(f147,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(sK1))
    | spl7_9 ),
    inference(avatar_component_clause,[],[f146])).

fof(f146,plain,
    ( spl7_9
  <=> m1_subset_1(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).

fof(f2643,plain,
    ( m1_subset_1(sK3,u1_struct_0(sK1))
    | ~ spl7_171 ),
    inference(resolution,[],[f2634,f53])).

fof(f2634,plain,
    ( r2_hidden(sK3,u1_struct_0(sK1))
    | ~ spl7_171 ),
    inference(avatar_component_clause,[],[f2633])).

fof(f2633,plain,
    ( spl7_171
  <=> r2_hidden(sK3,u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_171])])).

fof(f2638,plain,
    ( spl7_171
    | spl7_172
    | ~ spl7_170 ),
    inference(avatar_split_clause,[],[f2626,f2622,f2636,f2633])).

fof(f2622,plain,
    ( spl7_170
  <=> sP5(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_170])])).

fof(f2626,plain,
    ( r2_hidden(sK3,u1_struct_0(sK2))
    | r2_hidden(sK3,u1_struct_0(sK1))
    | ~ spl7_170 ),
    inference(resolution,[],[f2623,f46])).

fof(f46,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X1)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            | r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

fof(f2623,plain,
    ( sP5(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl7_170 ),
    inference(avatar_component_clause,[],[f2622])).

fof(f2624,plain,
    ( spl7_170
    | ~ spl7_17
    | ~ spl7_71 ),
    inference(avatar_split_clause,[],[f2620,f995,f205,f2622])).

fof(f205,plain,
    ( spl7_17
  <=> r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).

fof(f995,plain,
    ( spl7_71
  <=> u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).

fof(f2620,plain,
    ( sP5(sK3,u1_struct_0(sK2),u1_struct_0(sK1))
    | ~ spl7_17
    | ~ spl7_71 ),
    inference(resolution,[],[f998,f206])).

fof(f206,plain,
    ( r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl7_17 ),
    inference(avatar_component_clause,[],[f205])).

fof(f998,plain,
    ( ! [X0] :
        ( ~ r2_hidden(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
        | sP5(X0,u1_struct_0(sK2),u1_struct_0(sK1)) )
    | ~ spl7_71 ),
    inference(superposition,[],[f68,f996])).

fof(f996,plain,
    ( u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl7_71 ),
    inference(avatar_component_clause,[],[f995])).

fof(f68,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k2_xboole_0(X0,X1))
      | sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k2_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f2566,plain,
    ( ~ spl7_18
    | ~ spl7_32
    | ~ spl7_156 ),
    inference(avatar_split_clause,[],[f2558,f2168,f408,f208])).

fof(f208,plain,
    ( spl7_18
  <=> v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).

fof(f408,plain,
    ( spl7_32
  <=> m1_subset_1(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).

fof(f2168,plain,
    ( spl7_156
  <=> r2_hidden(sK3,sK6(k1_tsep_1(sK0,sK1,sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_156])])).

fof(f2558,plain,
    ( ~ v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl7_32
    | ~ spl7_156 ),
    inference(resolution,[],[f2175,f409])).

fof(f409,plain,
    ( m1_subset_1(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))
    | ~ spl7_32 ),
    inference(avatar_component_clause,[],[f408])).

fof(f2175,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_zfmisc_1(X0))
        | ~ v1_xboole_0(X0) )
    | ~ spl7_156 ),
    inference(resolution,[],[f2169,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ v1_xboole_0(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).

fof(f2169,plain,
    ( r2_hidden(sK3,sK6(k1_tsep_1(sK0,sK1,sK2),sK3))
    | ~ spl7_156 ),
    inference(avatar_component_clause,[],[f2168])).

fof(f2170,plain,
    ( spl7_156
    | ~ spl7_12
    | ~ spl7_21
    | ~ spl7_154 ),
    inference(avatar_split_clause,[],[f2166,f2158,f220,f158,f2168])).

fof(f158,plain,
    ( spl7_12
  <=> m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).

fof(f220,plain,
    ( spl7_21
  <=> m1_connsp_2(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_tsep_1(sK0,sK1,sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).

fof(f2158,plain,
    ( spl7_154
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
        | r2_hidden(X0,sK6(k1_tsep_1(sK0,sK1,sK2),sK3))
        | ~ m1_connsp_2(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_tsep_1(sK0,sK1,sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_154])])).

fof(f2166,plain,
    ( r2_hidden(sK3,sK6(k1_tsep_1(sK0,sK1,sK2),sK3))
    | ~ spl7_12
    | ~ spl7_21
    | ~ spl7_154 ),
    inference(subsumption_resolution,[],[f2165,f159])).

fof(f159,plain,
    ( m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl7_12 ),
    inference(avatar_component_clause,[],[f158])).

fof(f2165,plain,
    ( r2_hidden(sK3,sK6(k1_tsep_1(sK0,sK1,sK2),sK3))
    | ~ m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl7_21
    | ~ spl7_154 ),
    inference(resolution,[],[f2159,f221])).

fof(f221,plain,
    ( m1_connsp_2(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ spl7_21 ),
    inference(avatar_component_clause,[],[f220])).

fof(f2159,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_tsep_1(sK0,sK1,sK2),X0)
        | r2_hidden(X0,sK6(k1_tsep_1(sK0,sK1,sK2),sK3))
        | ~ m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) )
    | ~ spl7_154 ),
    inference(avatar_component_clause,[],[f2158])).

fof(f2160,plain,
    ( spl7_154
    | spl7_22
    | ~ spl7_23
    | ~ spl7_24
    | ~ spl7_32 ),
    inference(avatar_split_clause,[],[f414,f408,f238,f226,f223,f2158])).

fof(f223,plain,
    ( spl7_22
  <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).

fof(f226,plain,
    ( spl7_23
  <=> l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).

fof(f238,plain,
    ( spl7_24
  <=> v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).

fof(f414,plain,
    ( ! [X0] :
        ( v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
        | ~ m1_connsp_2(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_tsep_1(sK0,sK1,sK2),X0)
        | r2_hidden(X0,sK6(k1_tsep_1(sK0,sK1,sK2),sK3)) )
    | ~ spl7_23
    | ~ spl7_24
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f413,f405])).

fof(f405,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl7_23 ),
    inference(avatar_component_clause,[],[f226])).

fof(f413,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
        | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
        | ~ m1_connsp_2(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_tsep_1(sK0,sK1,sK2),X0)
        | r2_hidden(X0,sK6(k1_tsep_1(sK0,sK1,sK2),sK3)) )
    | ~ spl7_24
    | ~ spl7_32 ),
    inference(subsumption_resolution,[],[f411,f239])).

fof(f239,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl7_24 ),
    inference(avatar_component_clause,[],[f238])).

fof(f411,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
        | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
        | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
        | ~ m1_connsp_2(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_tsep_1(sK0,sK1,sK2),X0)
        | r2_hidden(X0,sK6(k1_tsep_1(sK0,sK1,sK2),sK3)) )
    | ~ spl7_32 ),
    inference(resolution,[],[f409,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ m1_subset_1(X2,u1_struct_0(X0))
      | ~ m1_connsp_2(X1,X0,X2)
      | r2_hidden(X2,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( r2_hidden(X2,X1)
              | ~ m1_connsp_2(X1,X0,X2)
              | ~ m1_subset_1(X2,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
             => ( m1_connsp_2(X1,X0,X2)
               => r2_hidden(X2,X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).

fof(f997,plain,
    ( spl7_71
    | spl7_22
    | spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_19
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f351,f254,f212,f96,f92,f88,f80,f76,f72,f223,f995])).

fof(f72,plain,
    ( spl7_1
  <=> v2_struct_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).

fof(f76,plain,
    ( spl7_2
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).

fof(f80,plain,
    ( spl7_3
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).

fof(f88,plain,
    ( spl7_5
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).

fof(f92,plain,
    ( spl7_6
  <=> m1_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).

fof(f96,plain,
    ( spl7_7
  <=> m1_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).

fof(f212,plain,
    ( spl7_19
  <=> v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).

fof(f254,plain,
    ( spl7_28
  <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).

fof(f351,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_19
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f350,f81])).

fof(f81,plain,
    ( ~ v2_struct_0(sK0)
    | spl7_3 ),
    inference(avatar_component_clause,[],[f80])).

fof(f350,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | spl7_1
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_19
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f349,f213])).

fof(f213,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl7_19 ),
    inference(avatar_component_clause,[],[f212])).

fof(f349,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | spl7_1
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f348,f93])).

fof(f93,plain,
    ( m1_pre_topc(sK2,sK0)
    | ~ spl7_6 ),
    inference(avatar_component_clause,[],[f92])).

fof(f348,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | spl7_1
    | spl7_2
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f347,f73])).

fof(f73,plain,
    ( ~ v2_struct_0(sK2)
    | spl7_1 ),
    inference(avatar_component_clause,[],[f72])).

fof(f347,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | spl7_2
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f346,f97])).

fof(f97,plain,
    ( m1_pre_topc(sK1,sK0)
    | ~ spl7_7 ),
    inference(avatar_component_clause,[],[f96])).

fof(f346,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | spl7_2
    | ~ spl7_5
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f345,f77])).

fof(f77,plain,
    ( ~ v2_struct_0(sK1)
    | spl7_2 ),
    inference(avatar_component_clause,[],[f76])).

fof(f345,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl7_5
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f330,f89])).

fof(f89,plain,
    ( l1_pre_topc(sK0)
    | ~ spl7_5 ),
    inference(avatar_component_clause,[],[f88])).

fof(f330,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(sK0)
    | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))
    | ~ spl7_28 ),
    inference(resolution,[],[f255,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ v1_pre_topc(k1_tsep_1(X0,X1,X2))
      | v2_struct_0(X0)
      | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2)) ) ),
    inference(equality_resolution,[],[f52])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X3)
      | ~ v1_pre_topc(X3)
      | ~ m1_pre_topc(X3,X0)
      | u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))
      | k1_tsep_1(X0,X1,X2) != X3 ) ),
    inference(cnf_transformation,[],[f18])).

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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f255,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | ~ spl7_28 ),
    inference(avatar_component_clause,[],[f254])).

fof(f553,plain,
    ( spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_22 ),
    inference(avatar_contradiction_clause,[],[f552])).

fof(f552,plain,
    ( $false
    | spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f551,f81])).

fof(f551,plain,
    ( v2_struct_0(sK0)
    | spl7_1
    | spl7_2
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f550,f93])).

fof(f550,plain,
    ( ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl7_1
    | spl7_2
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f549,f73])).

fof(f549,plain,
    ( v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl7_2
    | ~ spl7_5
    | ~ spl7_7
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f548,f97])).

fof(f548,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | spl7_2
    | ~ spl7_5
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f547,f77])).

fof(f547,plain,
    ( v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_5
    | ~ spl7_22 ),
    inference(subsumption_resolution,[],[f538,f89])).

fof(f538,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v2_struct_0(sK2)
    | ~ m1_pre_topc(sK2,sK0)
    | v2_struct_0(sK0)
    | ~ spl7_22 ),
    inference(resolution,[],[f224,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_struct_0(k1_tsep_1(X0,X1,X2))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f224,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl7_22 ),
    inference(avatar_component_clause,[],[f223])).

fof(f410,plain,
    ( spl7_32
    | spl7_22
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_21
    | ~ spl7_24
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f372,f254,f238,f220,f158,f88,f223,f408])).

fof(f372,plain,
    ( v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | m1_subset_1(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))
    | ~ spl7_5
    | ~ spl7_12
    | ~ spl7_21
    | ~ spl7_24
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f371,f159])).

fof(f371,plain,
    ( ~ m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | m1_subset_1(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))
    | ~ spl7_5
    | ~ spl7_21
    | ~ spl7_24
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f370,f352])).

fof(f352,plain,
    ( l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl7_5
    | ~ spl7_28 ),
    inference(subsumption_resolution,[],[f339,f89])).

fof(f339,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ spl7_28 ),
    inference(resolution,[],[f255,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f370,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | m1_subset_1(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))
    | ~ spl7_21
    | ~ spl7_24 ),
    inference(subsumption_resolution,[],[f369,f239])).

fof(f369,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | m1_subset_1(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))
    | ~ spl7_21 ),
    inference(resolution,[],[f221,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_connsp_2(X2,X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_connsp_2(X2,X0,X1) )
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X2] :
          ( m1_connsp_2(X2,X0,X1)
         => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).

fof(f406,plain,
    ( spl7_23
    | ~ spl7_5
    | ~ spl7_28 ),
    inference(avatar_split_clause,[],[f352,f254,f88,f226])).

fof(f256,plain,
    ( spl7_28
    | spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f202,f96,f92,f88,f80,f76,f72,f254])).

fof(f202,plain,
    ( m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f200,f73])).

fof(f200,plain,
    ( v2_struct_0(sK2)
    | m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(resolution,[],[f137,f93])).

fof(f137,plain,
    ( ! [X3] :
        ( ~ m1_pre_topc(X3,sK0)
        | v2_struct_0(X3)
        | m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK0) )
    | spl7_2
    | spl7_3
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f136,f81])).

fof(f136,plain,
    ( ! [X3] :
        ( v2_struct_0(sK0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK0) )
    | spl7_2
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f135,f77])).

fof(f135,plain,
    ( ! [X3] :
        ( v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK0) )
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f124,f89])).

fof(f124,plain,
    ( ! [X3] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | v2_struct_0(X3)
        | ~ m1_pre_topc(X3,sK0)
        | m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK0) )
    | ~ spl7_7 ),
    inference(resolution,[],[f97,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f240,plain,
    ( spl7_24
    | spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f185,f96,f92,f88,f84,f80,f76,f72,f238])).

fof(f84,plain,
    ( spl7_4
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).

fof(f185,plain,
    ( v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f183,f73])).

fof(f183,plain,
    ( v2_struct_0(sK2)
    | v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(resolution,[],[f134,f93])).

fof(f134,plain,
    ( ! [X1] :
        ( ~ m1_pre_topc(X1,sK0)
        | v2_struct_0(X1)
        | v2_pre_topc(k1_tsep_1(sK0,sK1,X1)) )
    | spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f133,f81])).

fof(f133,plain,
    ( ! [X1] :
        ( v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_pre_topc(k1_tsep_1(sK0,sK1,X1)) )
    | spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f132,f77])).

fof(f132,plain,
    ( ! [X1] :
        ( v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_pre_topc(k1_tsep_1(sK0,sK1,X1)) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f131,f89])).

fof(f131,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_pre_topc(k1_tsep_1(sK0,sK1,X1)) )
    | ~ spl7_4
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f122,f85])).

fof(f85,plain,
    ( v2_pre_topc(sK0)
    | ~ spl7_4 ),
    inference(avatar_component_clause,[],[f84])).

fof(f122,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | v2_struct_0(X1)
        | ~ m1_pre_topc(X1,sK0)
        | v2_pre_topc(k1_tsep_1(sK0,sK1,X1)) )
    | ~ spl7_7 ),
    inference(resolution,[],[f97,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v2_pre_topc(k1_tsep_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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
    inference(flattening,[],[f28])).

fof(f28,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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

fof(f228,plain,
    ( spl7_21
    | spl7_22
    | ~ spl7_23
    | spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f186,f158,f96,f92,f88,f84,f80,f76,f72,f226,f223,f220])).

fof(f186,plain,
    ( ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | m1_connsp_2(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_tsep_1(sK0,sK1,sK2),sK3)
    | spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7
    | ~ spl7_12 ),
    inference(subsumption_resolution,[],[f161,f185])).

fof(f161,plain,
    ( ~ v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | ~ l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | v2_struct_0(k1_tsep_1(sK0,sK1,sK2))
    | m1_connsp_2(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_tsep_1(sK0,sK1,sK2),sK3)
    | ~ spl7_12 ),
    inference(resolution,[],[f159,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_connsp_2(sK6(X0,X1),X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ? [X2] : m1_connsp_2(X2,X0,X1)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,u1_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ? [X2] : m1_connsp_2(X2,X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).

fof(f214,plain,
    ( spl7_19
    | spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(avatar_split_clause,[],[f177,f96,f92,f88,f84,f80,f76,f72,f212])).

fof(f177,plain,
    ( v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | spl7_1
    | spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f175,f73])).

fof(f175,plain,
    ( v2_struct_0(sK2)
    | v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))
    | spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_6
    | ~ spl7_7 ),
    inference(resolution,[],[f130,f93])).

fof(f130,plain,
    ( ! [X0] :
        ( ~ m1_pre_topc(X0,sK0)
        | v2_struct_0(X0)
        | v1_pre_topc(k1_tsep_1(sK0,sK1,X0)) )
    | spl7_2
    | spl7_3
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f129,f81])).

fof(f129,plain,
    ( ! [X0] :
        ( v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v1_pre_topc(k1_tsep_1(sK0,sK1,X0)) )
    | spl7_2
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f128,f77])).

fof(f128,plain,
    ( ! [X0] :
        ( v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v1_pre_topc(k1_tsep_1(sK0,sK1,X0)) )
    | ~ spl7_4
    | ~ spl7_5
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f127,f89])).

fof(f127,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v1_pre_topc(k1_tsep_1(sK0,sK1,X0)) )
    | ~ spl7_4
    | ~ spl7_7 ),
    inference(subsumption_resolution,[],[f121,f85])).

fof(f121,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(sK1)
        | v2_struct_0(sK0)
        | v2_struct_0(X0)
        | ~ m1_pre_topc(X0,sK0)
        | v1_pre_topc(k1_tsep_1(sK0,sK1,X0)) )
    | ~ spl7_7 ),
    inference(resolution,[],[f97,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | v2_struct_0(X2)
      | ~ m1_pre_topc(X2,X0)
      | v1_pre_topc(k1_tsep_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f210,plain,
    ( spl7_17
    | spl7_18
    | ~ spl7_12 ),
    inference(avatar_split_clause,[],[f162,f158,f208,f205])).

fof(f162,plain,
    ( v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))
    | ~ spl7_12 ),
    inference(resolution,[],[f159,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f160,plain,(
    spl7_12 ),
    inference(avatar_split_clause,[],[f36,f158])).

fof(f36,plain,(
    m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ! [X4] :
                      ( X3 != X4
                      | ~ m1_subset_1(X4,u1_struct_0(X2)) )
                  & ! [X5] :
                      ( X3 != X5
                      | ~ m1_subset_1(X5,u1_struct_0(X1)) )
                  & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) )
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,plain,(
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
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X2))
                           => X3 != X4 )
                        & ! [X5] :
                            ( m1_subset_1(X5,u1_struct_0(X1))
                           => X3 != X5 ) ) ) ) ) ) ),
    inference(rectify,[],[f13])).

fof(f13,negated_conjecture,(
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
                    ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                   => ~ ( ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X2))
                           => X3 != X4 )
                        & ! [X4] :
                            ( m1_subset_1(X4,u1_struct_0(X1))
                           => X3 != X4 ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
                  ( m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))
                 => ~ ( ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X2))
                         => X3 != X4 )
                      & ! [X4] :
                          ( m1_subset_1(X4,u1_struct_0(X1))
                         => X3 != X4 ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tmap_1)).

fof(f156,plain,(
    ~ spl7_11 ),
    inference(avatar_split_clause,[],[f67,f154])).

fof(f67,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK2)) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,u1_struct_0(sK2))
      | sK3 != X4 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f148,plain,(
    ~ spl7_9 ),
    inference(avatar_split_clause,[],[f66,f146])).

fof(f66,plain,(
    ~ m1_subset_1(sK3,u1_struct_0(sK1)) ),
    inference(equality_resolution,[],[f35])).

fof(f35,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,u1_struct_0(sK1))
      | sK3 != X5 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f98,plain,(
    spl7_7 ),
    inference(avatar_split_clause,[],[f40,f96])).

fof(f40,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f94,plain,(
    spl7_6 ),
    inference(avatar_split_clause,[],[f38,f92])).

fof(f38,plain,(
    m1_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f90,plain,(
    spl7_5 ),
    inference(avatar_split_clause,[],[f43,f88])).

fof(f43,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f86,plain,(
    spl7_4 ),
    inference(avatar_split_clause,[],[f42,f84])).

fof(f42,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f82,plain,(
    ~ spl7_3 ),
    inference(avatar_split_clause,[],[f41,f80])).

fof(f41,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f78,plain,(
    ~ spl7_2 ),
    inference(avatar_split_clause,[],[f39,f76])).

fof(f39,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f74,plain,(
    ~ spl7_1 ),
    inference(avatar_split_clause,[],[f37,f72])).

fof(f37,plain,(
    ~ v2_struct_0(sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:39:51 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.47  % (24379)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.48  % (24383)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  % (24379)Refutation not found, incomplete strategy% (24379)------------------------------
% 0.21/0.48  % (24379)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (24387)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.48  % (24379)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (24379)Memory used [KB]: 10618
% 0.21/0.48  % (24379)Time elapsed: 0.062 s
% 0.21/0.48  % (24379)------------------------------
% 0.21/0.48  % (24379)------------------------------
% 0.21/0.49  % (24385)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (24391)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.49  % (24393)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.50  % (24392)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (24384)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.50  % (24386)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.50  % (24381)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  % (24378)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (24382)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  % (24380)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.51  % (24394)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.51  % (24389)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.51  % (24396)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  % (24398)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.21/0.51  % (24398)Refutation not found, incomplete strategy% (24398)------------------------------
% 0.21/0.51  % (24398)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (24398)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.51  
% 0.21/0.51  % (24398)Memory used [KB]: 10618
% 0.21/0.51  % (24398)Time elapsed: 0.108 s
% 0.21/0.51  % (24398)------------------------------
% 0.21/0.51  % (24398)------------------------------
% 0.21/0.52  % (24397)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.52  % (24395)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.52  % (24388)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.52  % (24388)Refutation not found, incomplete strategy% (24388)------------------------------
% 0.21/0.52  % (24388)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (24388)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (24388)Memory used [KB]: 6012
% 0.21/0.52  % (24388)Time elapsed: 0.087 s
% 0.21/0.52  % (24388)------------------------------
% 0.21/0.52  % (24388)------------------------------
% 0.21/0.52  % (24390)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 2.31/0.66  % (24378)Refutation found. Thanks to Tanya!
% 2.31/0.66  % SZS status Theorem for theBenchmark
% 2.31/0.66  % SZS output start Proof for theBenchmark
% 2.31/0.66  fof(f2658,plain,(
% 2.31/0.66    $false),
% 2.31/0.66    inference(avatar_sat_refutation,[],[f74,f78,f82,f86,f90,f94,f98,f148,f156,f160,f210,f214,f228,f240,f256,f406,f410,f553,f997,f2160,f2170,f2566,f2624,f2638,f2647,f2657])).
% 2.31/0.66  fof(f2657,plain,(
% 2.31/0.66    spl7_11 | ~spl7_172),
% 2.31/0.66    inference(avatar_contradiction_clause,[],[f2656])).
% 2.31/0.66  fof(f2656,plain,(
% 2.31/0.66    $false | (spl7_11 | ~spl7_172)),
% 2.31/0.66    inference(subsumption_resolution,[],[f2653,f155])).
% 2.31/0.66  fof(f155,plain,(
% 2.31/0.66    ~m1_subset_1(sK3,u1_struct_0(sK2)) | spl7_11),
% 2.31/0.66    inference(avatar_component_clause,[],[f154])).
% 2.31/0.66  fof(f154,plain,(
% 2.31/0.66    spl7_11 <=> m1_subset_1(sK3,u1_struct_0(sK2))),
% 2.31/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_11])])).
% 2.31/0.66  fof(f2653,plain,(
% 2.31/0.66    m1_subset_1(sK3,u1_struct_0(sK2)) | ~spl7_172),
% 2.31/0.66    inference(resolution,[],[f2637,f53])).
% 2.31/0.66  fof(f53,plain,(
% 2.31/0.66    ( ! [X0,X1] : (~r2_hidden(X0,X1) | m1_subset_1(X0,X1)) )),
% 2.31/0.66    inference(cnf_transformation,[],[f19])).
% 2.31/0.66  fof(f19,plain,(
% 2.31/0.66    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 2.31/0.66    inference(ennf_transformation,[],[f2])).
% 2.31/0.66  fof(f2,axiom,(
% 2.31/0.66    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 2.31/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 2.31/0.66  fof(f2637,plain,(
% 2.31/0.66    r2_hidden(sK3,u1_struct_0(sK2)) | ~spl7_172),
% 2.31/0.66    inference(avatar_component_clause,[],[f2636])).
% 2.31/0.66  fof(f2636,plain,(
% 2.31/0.66    spl7_172 <=> r2_hidden(sK3,u1_struct_0(sK2))),
% 2.31/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_172])])).
% 2.31/0.66  fof(f2647,plain,(
% 2.31/0.66    spl7_9 | ~spl7_171),
% 2.31/0.66    inference(avatar_contradiction_clause,[],[f2646])).
% 2.31/0.66  fof(f2646,plain,(
% 2.31/0.66    $false | (spl7_9 | ~spl7_171)),
% 2.31/0.66    inference(subsumption_resolution,[],[f2643,f147])).
% 2.31/0.66  fof(f147,plain,(
% 2.31/0.66    ~m1_subset_1(sK3,u1_struct_0(sK1)) | spl7_9),
% 2.31/0.66    inference(avatar_component_clause,[],[f146])).
% 2.31/0.66  fof(f146,plain,(
% 2.31/0.66    spl7_9 <=> m1_subset_1(sK3,u1_struct_0(sK1))),
% 2.31/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_9])])).
% 2.31/0.66  fof(f2643,plain,(
% 2.31/0.66    m1_subset_1(sK3,u1_struct_0(sK1)) | ~spl7_171),
% 2.31/0.66    inference(resolution,[],[f2634,f53])).
% 2.31/0.66  fof(f2634,plain,(
% 2.31/0.66    r2_hidden(sK3,u1_struct_0(sK1)) | ~spl7_171),
% 2.31/0.66    inference(avatar_component_clause,[],[f2633])).
% 2.31/0.66  fof(f2633,plain,(
% 2.31/0.66    spl7_171 <=> r2_hidden(sK3,u1_struct_0(sK1))),
% 2.31/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_171])])).
% 2.31/0.66  fof(f2638,plain,(
% 2.31/0.66    spl7_171 | spl7_172 | ~spl7_170),
% 2.31/0.66    inference(avatar_split_clause,[],[f2626,f2622,f2636,f2633])).
% 2.31/0.66  fof(f2622,plain,(
% 2.31/0.66    spl7_170 <=> sP5(sK3,u1_struct_0(sK2),u1_struct_0(sK1))),
% 2.31/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_170])])).
% 2.31/0.66  fof(f2626,plain,(
% 2.31/0.66    r2_hidden(sK3,u1_struct_0(sK2)) | r2_hidden(sK3,u1_struct_0(sK1)) | ~spl7_170),
% 2.31/0.66    inference(resolution,[],[f2623,f46])).
% 2.31/0.66  fof(f46,plain,(
% 2.31/0.66    ( ! [X0,X3,X1] : (~sP5(X3,X1,X0) | r2_hidden(X3,X1) | r2_hidden(X3,X0)) )),
% 2.31/0.66    inference(cnf_transformation,[],[f1])).
% 2.31/0.66  fof(f1,axiom,(
% 2.31/0.66    ! [X0,X1,X2] : (k2_xboole_0(X0,X1) = X2 <=> ! [X3] : (r2_hidden(X3,X2) <=> (r2_hidden(X3,X1) | r2_hidden(X3,X0))))),
% 2.31/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).
% 2.31/0.66  fof(f2623,plain,(
% 2.31/0.66    sP5(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | ~spl7_170),
% 2.31/0.66    inference(avatar_component_clause,[],[f2622])).
% 2.31/0.66  fof(f2624,plain,(
% 2.31/0.66    spl7_170 | ~spl7_17 | ~spl7_71),
% 2.31/0.66    inference(avatar_split_clause,[],[f2620,f995,f205,f2622])).
% 2.31/0.66  fof(f205,plain,(
% 2.31/0.66    spl7_17 <=> r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 2.31/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_17])])).
% 2.31/0.66  fof(f995,plain,(
% 2.31/0.66    spl7_71 <=> u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2))),
% 2.31/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_71])])).
% 2.31/0.66  fof(f2620,plain,(
% 2.31/0.66    sP5(sK3,u1_struct_0(sK2),u1_struct_0(sK1)) | (~spl7_17 | ~spl7_71)),
% 2.31/0.66    inference(resolution,[],[f998,f206])).
% 2.31/0.66  fof(f206,plain,(
% 2.31/0.66    r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~spl7_17),
% 2.31/0.66    inference(avatar_component_clause,[],[f205])).
% 2.31/0.66  fof(f998,plain,(
% 2.31/0.66    ( ! [X0] : (~r2_hidden(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | sP5(X0,u1_struct_0(sK2),u1_struct_0(sK1))) ) | ~spl7_71),
% 2.31/0.66    inference(superposition,[],[f68,f996])).
% 2.31/0.66  fof(f996,plain,(
% 2.31/0.66    u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | ~spl7_71),
% 2.31/0.66    inference(avatar_component_clause,[],[f995])).
% 2.31/0.66  fof(f68,plain,(
% 2.31/0.66    ( ! [X0,X3,X1] : (~r2_hidden(X3,k2_xboole_0(X0,X1)) | sP5(X3,X1,X0)) )),
% 2.31/0.66    inference(equality_resolution,[],[f48])).
% 2.31/0.66  fof(f48,plain,(
% 2.31/0.66    ( ! [X2,X0,X3,X1] : (sP5(X3,X1,X0) | ~r2_hidden(X3,X2) | k2_xboole_0(X0,X1) != X2) )),
% 2.31/0.66    inference(cnf_transformation,[],[f1])).
% 2.31/0.66  fof(f2566,plain,(
% 2.31/0.66    ~spl7_18 | ~spl7_32 | ~spl7_156),
% 2.31/0.66    inference(avatar_split_clause,[],[f2558,f2168,f408,f208])).
% 2.31/0.66  fof(f208,plain,(
% 2.31/0.66    spl7_18 <=> v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 2.31/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_18])])).
% 2.31/0.66  fof(f408,plain,(
% 2.31/0.66    spl7_32 <=> m1_subset_1(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))))),
% 2.31/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_32])])).
% 2.31/0.66  fof(f2168,plain,(
% 2.31/0.66    spl7_156 <=> r2_hidden(sK3,sK6(k1_tsep_1(sK0,sK1,sK2),sK3))),
% 2.31/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_156])])).
% 2.31/0.66  fof(f2558,plain,(
% 2.31/0.66    ~v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | (~spl7_32 | ~spl7_156)),
% 2.31/0.66    inference(resolution,[],[f2175,f409])).
% 2.31/0.66  fof(f409,plain,(
% 2.31/0.66    m1_subset_1(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) | ~spl7_32),
% 2.31/0.66    inference(avatar_component_clause,[],[f408])).
% 2.31/0.66  fof(f2175,plain,(
% 2.31/0.66    ( ! [X0] : (~m1_subset_1(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) ) | ~spl7_156),
% 2.31/0.66    inference(resolution,[],[f2169,f64])).
% 2.31/0.66  fof(f64,plain,(
% 2.31/0.66    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~v1_xboole_0(X2)) )),
% 2.31/0.66    inference(cnf_transformation,[],[f31])).
% 2.31/0.66  fof(f31,plain,(
% 2.31/0.66    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 2.31/0.66    inference(ennf_transformation,[],[f4])).
% 2.31/0.66  fof(f4,axiom,(
% 2.31/0.66    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 2.31/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_subset)).
% 2.31/0.66  fof(f2169,plain,(
% 2.31/0.66    r2_hidden(sK3,sK6(k1_tsep_1(sK0,sK1,sK2),sK3)) | ~spl7_156),
% 2.31/0.66    inference(avatar_component_clause,[],[f2168])).
% 2.31/0.66  fof(f2170,plain,(
% 2.31/0.66    spl7_156 | ~spl7_12 | ~spl7_21 | ~spl7_154),
% 2.31/0.66    inference(avatar_split_clause,[],[f2166,f2158,f220,f158,f2168])).
% 2.31/0.66  fof(f158,plain,(
% 2.31/0.66    spl7_12 <=> m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 2.31/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_12])])).
% 2.31/0.66  fof(f220,plain,(
% 2.31/0.66    spl7_21 <=> m1_connsp_2(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_tsep_1(sK0,sK1,sK2),sK3)),
% 2.31/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_21])])).
% 2.31/0.66  fof(f2158,plain,(
% 2.31/0.66    spl7_154 <=> ! [X0] : (~m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | r2_hidden(X0,sK6(k1_tsep_1(sK0,sK1,sK2),sK3)) | ~m1_connsp_2(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_tsep_1(sK0,sK1,sK2),X0))),
% 2.31/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_154])])).
% 2.31/0.66  fof(f2166,plain,(
% 2.31/0.66    r2_hidden(sK3,sK6(k1_tsep_1(sK0,sK1,sK2),sK3)) | (~spl7_12 | ~spl7_21 | ~spl7_154)),
% 2.31/0.66    inference(subsumption_resolution,[],[f2165,f159])).
% 2.31/0.66  fof(f159,plain,(
% 2.31/0.66    m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~spl7_12),
% 2.31/0.66    inference(avatar_component_clause,[],[f158])).
% 2.31/0.66  fof(f2165,plain,(
% 2.31/0.66    r2_hidden(sK3,sK6(k1_tsep_1(sK0,sK1,sK2),sK3)) | ~m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | (~spl7_21 | ~spl7_154)),
% 2.31/0.66    inference(resolution,[],[f2159,f221])).
% 2.31/0.66  fof(f221,plain,(
% 2.31/0.66    m1_connsp_2(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_tsep_1(sK0,sK1,sK2),sK3) | ~spl7_21),
% 2.31/0.66    inference(avatar_component_clause,[],[f220])).
% 2.31/0.66  fof(f2159,plain,(
% 2.31/0.66    ( ! [X0] : (~m1_connsp_2(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_tsep_1(sK0,sK1,sK2),X0) | r2_hidden(X0,sK6(k1_tsep_1(sK0,sK1,sK2),sK3)) | ~m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) ) | ~spl7_154),
% 2.31/0.66    inference(avatar_component_clause,[],[f2158])).
% 2.31/0.66  fof(f2160,plain,(
% 2.31/0.66    spl7_154 | spl7_22 | ~spl7_23 | ~spl7_24 | ~spl7_32),
% 2.31/0.66    inference(avatar_split_clause,[],[f414,f408,f238,f226,f223,f2158])).
% 2.31/0.66  fof(f223,plain,(
% 2.31/0.66    spl7_22 <=> v2_struct_0(k1_tsep_1(sK0,sK1,sK2))),
% 2.31/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_22])])).
% 2.31/0.66  fof(f226,plain,(
% 2.31/0.66    spl7_23 <=> l1_pre_topc(k1_tsep_1(sK0,sK1,sK2))),
% 2.31/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_23])])).
% 2.31/0.66  fof(f238,plain,(
% 2.31/0.66    spl7_24 <=> v2_pre_topc(k1_tsep_1(sK0,sK1,sK2))),
% 2.31/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_24])])).
% 2.31/0.66  fof(f414,plain,(
% 2.31/0.66    ( ! [X0] : (v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~m1_connsp_2(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_tsep_1(sK0,sK1,sK2),X0) | r2_hidden(X0,sK6(k1_tsep_1(sK0,sK1,sK2),sK3))) ) | (~spl7_23 | ~spl7_24 | ~spl7_32)),
% 2.31/0.66    inference(subsumption_resolution,[],[f413,f405])).
% 2.31/0.66  fof(f405,plain,(
% 2.31/0.66    l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~spl7_23),
% 2.31/0.66    inference(avatar_component_clause,[],[f226])).
% 2.31/0.66  fof(f413,plain,(
% 2.31/0.66    ( ! [X0] : (~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~m1_connsp_2(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_tsep_1(sK0,sK1,sK2),X0) | r2_hidden(X0,sK6(k1_tsep_1(sK0,sK1,sK2),sK3))) ) | (~spl7_24 | ~spl7_32)),
% 2.31/0.66    inference(subsumption_resolution,[],[f411,f239])).
% 2.31/0.66  fof(f239,plain,(
% 2.31/0.66    v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~spl7_24),
% 2.31/0.66    inference(avatar_component_clause,[],[f238])).
% 2.31/0.66  fof(f411,plain,(
% 2.31/0.66    ( ! [X0] : (~v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~m1_subset_1(X0,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~m1_connsp_2(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_tsep_1(sK0,sK1,sK2),X0) | r2_hidden(X0,sK6(k1_tsep_1(sK0,sK1,sK2),sK3))) ) | ~spl7_32),
% 2.31/0.66    inference(resolution,[],[f409,f56])).
% 2.31/0.66  fof(f56,plain,(
% 2.31/0.66    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~m1_subset_1(X2,u1_struct_0(X0)) | ~m1_connsp_2(X1,X0,X2) | r2_hidden(X2,X1)) )),
% 2.31/0.66    inference(cnf_transformation,[],[f25])).
% 2.31/0.66  fof(f25,plain,(
% 2.31/0.66    ! [X0] : (! [X1] : (! [X2] : (r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.31/0.66    inference(flattening,[],[f24])).
% 2.31/0.66  fof(f24,plain,(
% 2.31/0.66    ! [X0] : (! [X1] : (! [X2] : ((r2_hidden(X2,X1) | ~m1_connsp_2(X1,X0,X2)) | ~m1_subset_1(X2,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.31/0.66    inference(ennf_transformation,[],[f8])).
% 2.31/0.66  fof(f8,axiom,(
% 2.31/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) => (m1_connsp_2(X1,X0,X2) => r2_hidden(X2,X1)))))),
% 2.31/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_connsp_2)).
% 2.31/0.66  fof(f997,plain,(
% 2.31/0.66    spl7_71 | spl7_22 | spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_19 | ~spl7_28),
% 2.31/0.66    inference(avatar_split_clause,[],[f351,f254,f212,f96,f92,f88,f80,f76,f72,f223,f995])).
% 2.31/0.66  fof(f72,plain,(
% 2.31/0.66    spl7_1 <=> v2_struct_0(sK2)),
% 2.31/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_1])])).
% 2.31/0.66  fof(f76,plain,(
% 2.31/0.66    spl7_2 <=> v2_struct_0(sK1)),
% 2.31/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_2])])).
% 2.31/0.66  fof(f80,plain,(
% 2.31/0.66    spl7_3 <=> v2_struct_0(sK0)),
% 2.31/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_3])])).
% 2.31/0.66  fof(f88,plain,(
% 2.31/0.66    spl7_5 <=> l1_pre_topc(sK0)),
% 2.31/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_5])])).
% 2.31/0.66  fof(f92,plain,(
% 2.31/0.66    spl7_6 <=> m1_pre_topc(sK2,sK0)),
% 2.31/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_6])])).
% 2.31/0.66  fof(f96,plain,(
% 2.31/0.66    spl7_7 <=> m1_pre_topc(sK1,sK0)),
% 2.31/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_7])])).
% 2.31/0.66  fof(f212,plain,(
% 2.31/0.66    spl7_19 <=> v1_pre_topc(k1_tsep_1(sK0,sK1,sK2))),
% 2.31/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_19])])).
% 2.31/0.66  fof(f254,plain,(
% 2.31/0.66    spl7_28 <=> m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0)),
% 2.31/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_28])])).
% 2.31/0.66  fof(f351,plain,(
% 2.31/0.66    v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | (spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_19 | ~spl7_28)),
% 2.31/0.66    inference(subsumption_resolution,[],[f350,f81])).
% 2.31/0.66  fof(f81,plain,(
% 2.31/0.66    ~v2_struct_0(sK0) | spl7_3),
% 2.31/0.66    inference(avatar_component_clause,[],[f80])).
% 2.31/0.66  fof(f350,plain,(
% 2.31/0.66    v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK0) | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | (spl7_1 | spl7_2 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_19 | ~spl7_28)),
% 2.31/0.66    inference(subsumption_resolution,[],[f349,f213])).
% 2.31/0.66  fof(f213,plain,(
% 2.31/0.66    v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~spl7_19),
% 2.31/0.66    inference(avatar_component_clause,[],[f212])).
% 2.31/0.66  fof(f349,plain,(
% 2.31/0.66    v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK0) | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | (spl7_1 | spl7_2 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_28)),
% 2.31/0.66    inference(subsumption_resolution,[],[f348,f93])).
% 2.31/0.66  fof(f93,plain,(
% 2.31/0.66    m1_pre_topc(sK2,sK0) | ~spl7_6),
% 2.31/0.66    inference(avatar_component_clause,[],[f92])).
% 2.31/0.66  fof(f348,plain,(
% 2.31/0.66    ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK0) | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | (spl7_1 | spl7_2 | ~spl7_5 | ~spl7_7 | ~spl7_28)),
% 2.31/0.66    inference(subsumption_resolution,[],[f347,f73])).
% 2.31/0.66  fof(f73,plain,(
% 2.31/0.66    ~v2_struct_0(sK2) | spl7_1),
% 2.31/0.66    inference(avatar_component_clause,[],[f72])).
% 2.31/0.66  fof(f347,plain,(
% 2.31/0.66    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK0) | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | (spl7_2 | ~spl7_5 | ~spl7_7 | ~spl7_28)),
% 2.31/0.66    inference(subsumption_resolution,[],[f346,f97])).
% 2.31/0.66  fof(f97,plain,(
% 2.31/0.66    m1_pre_topc(sK1,sK0) | ~spl7_7),
% 2.31/0.66    inference(avatar_component_clause,[],[f96])).
% 2.31/0.66  fof(f346,plain,(
% 2.31/0.66    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK0) | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | (spl7_2 | ~spl7_5 | ~spl7_28)),
% 2.31/0.66    inference(subsumption_resolution,[],[f345,f77])).
% 2.31/0.66  fof(f77,plain,(
% 2.31/0.66    ~v2_struct_0(sK1) | spl7_2),
% 2.31/0.66    inference(avatar_component_clause,[],[f76])).
% 2.31/0.66  fof(f345,plain,(
% 2.31/0.66    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK0) | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | (~spl7_5 | ~spl7_28)),
% 2.31/0.66    inference(subsumption_resolution,[],[f330,f89])).
% 2.31/0.66  fof(f89,plain,(
% 2.31/0.66    l1_pre_topc(sK0) | ~spl7_5),
% 2.31/0.66    inference(avatar_component_clause,[],[f88])).
% 2.31/0.66  fof(f330,plain,(
% 2.31/0.66    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(sK0) | u1_struct_0(k1_tsep_1(sK0,sK1,sK2)) = k2_xboole_0(u1_struct_0(sK1),u1_struct_0(sK2)) | ~spl7_28),
% 2.31/0.66    inference(resolution,[],[f255,f70])).
% 2.31/0.66  fof(f70,plain,(
% 2.31/0.66    ( ! [X2,X0,X1] : (~m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~v1_pre_topc(k1_tsep_1(X0,X1,X2)) | v2_struct_0(X0) | k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) = u1_struct_0(k1_tsep_1(X0,X1,X2))) )),
% 2.31/0.66    inference(equality_resolution,[],[f52])).
% 2.31/0.66  fof(f52,plain,(
% 2.31/0.66    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X3) | ~v1_pre_topc(X3) | ~m1_pre_topc(X3,X0) | u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)) | k1_tsep_1(X0,X1,X2) != X3) )),
% 2.31/0.66    inference(cnf_transformation,[],[f18])).
% 2.31/0.66  fof(f18,plain,(
% 2.31/0.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | ~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3)) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2)) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.31/0.66    inference(flattening,[],[f17])).
% 2.31/0.66  fof(f17,plain,(
% 2.31/0.66    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2))) | (~m1_pre_topc(X3,X0) | ~v1_pre_topc(X3) | v2_struct_0(X3))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.31/0.66    inference(ennf_transformation,[],[f9])).
% 2.31/0.66  fof(f9,axiom,(
% 2.31/0.66    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : ((m1_pre_topc(X3,X0) & v1_pre_topc(X3) & ~v2_struct_0(X3)) => (k1_tsep_1(X0,X1,X2) = X3 <=> u1_struct_0(X3) = k2_xboole_0(u1_struct_0(X1),u1_struct_0(X2)))))))),
% 2.31/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tsep_1)).
% 2.31/0.66  fof(f255,plain,(
% 2.31/0.66    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | ~spl7_28),
% 2.31/0.66    inference(avatar_component_clause,[],[f254])).
% 2.31/0.66  fof(f553,plain,(
% 2.31/0.66    spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_22),
% 2.31/0.66    inference(avatar_contradiction_clause,[],[f552])).
% 2.31/0.66  fof(f552,plain,(
% 2.31/0.66    $false | (spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_22)),
% 2.31/0.66    inference(subsumption_resolution,[],[f551,f81])).
% 2.31/0.66  fof(f551,plain,(
% 2.31/0.66    v2_struct_0(sK0) | (spl7_1 | spl7_2 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_22)),
% 2.31/0.66    inference(subsumption_resolution,[],[f550,f93])).
% 2.31/0.66  fof(f550,plain,(
% 2.31/0.66    ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (spl7_1 | spl7_2 | ~spl7_5 | ~spl7_7 | ~spl7_22)),
% 2.31/0.66    inference(subsumption_resolution,[],[f549,f73])).
% 2.31/0.66  fof(f549,plain,(
% 2.31/0.66    v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (spl7_2 | ~spl7_5 | ~spl7_7 | ~spl7_22)),
% 2.31/0.66    inference(subsumption_resolution,[],[f548,f97])).
% 2.31/0.66  fof(f548,plain,(
% 2.31/0.66    ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (spl7_2 | ~spl7_5 | ~spl7_22)),
% 2.31/0.66    inference(subsumption_resolution,[],[f547,f77])).
% 2.31/0.66  fof(f547,plain,(
% 2.31/0.66    v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | (~spl7_5 | ~spl7_22)),
% 2.31/0.66    inference(subsumption_resolution,[],[f538,f89])).
% 2.31/0.66  fof(f538,plain,(
% 2.31/0.66    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~m1_pre_topc(sK1,sK0) | v2_struct_0(sK2) | ~m1_pre_topc(sK2,sK0) | v2_struct_0(sK0) | ~spl7_22),
% 2.31/0.66    inference(resolution,[],[f224,f57])).
% 2.31/0.66  fof(f57,plain,(
% 2.31/0.66    ( ! [X2,X0,X1] : (~v2_struct_0(k1_tsep_1(X0,X1,X2)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_struct_0(X0)) )),
% 2.31/0.66    inference(cnf_transformation,[],[f27])).
% 2.31/0.66  fof(f27,plain,(
% 2.31/0.66    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 2.31/0.66    inference(flattening,[],[f26])).
% 2.31/0.66  fof(f26,plain,(
% 2.31/0.66    ! [X0,X1,X2] : ((m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 2.31/0.66    inference(ennf_transformation,[],[f10])).
% 2.31/0.66  fof(f10,axiom,(
% 2.31/0.66    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_pre_topc(k1_tsep_1(X0,X1,X2),X0) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 2.31/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tsep_1)).
% 2.31/0.66  fof(f224,plain,(
% 2.31/0.66    v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | ~spl7_22),
% 2.31/0.66    inference(avatar_component_clause,[],[f223])).
% 2.31/0.66  fof(f410,plain,(
% 2.31/0.66    spl7_32 | spl7_22 | ~spl7_5 | ~spl7_12 | ~spl7_21 | ~spl7_24 | ~spl7_28),
% 2.31/0.66    inference(avatar_split_clause,[],[f372,f254,f238,f220,f158,f88,f223,f408])).
% 2.31/0.66  fof(f372,plain,(
% 2.31/0.66    v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | m1_subset_1(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) | (~spl7_5 | ~spl7_12 | ~spl7_21 | ~spl7_24 | ~spl7_28)),
% 2.31/0.66    inference(subsumption_resolution,[],[f371,f159])).
% 2.31/0.66  fof(f371,plain,(
% 2.31/0.66    ~m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | m1_subset_1(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) | (~spl7_5 | ~spl7_21 | ~spl7_24 | ~spl7_28)),
% 2.31/0.66    inference(subsumption_resolution,[],[f370,f352])).
% 2.31/0.66  fof(f352,plain,(
% 2.31/0.66    l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | (~spl7_5 | ~spl7_28)),
% 2.31/0.66    inference(subsumption_resolution,[],[f339,f89])).
% 2.31/0.66  fof(f339,plain,(
% 2.31/0.66    ~l1_pre_topc(sK0) | l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~spl7_28),
% 2.31/0.66    inference(resolution,[],[f255,f63])).
% 2.31/0.66  fof(f63,plain,(
% 2.31/0.66    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 2.31/0.66    inference(cnf_transformation,[],[f30])).
% 2.31/0.66  fof(f30,plain,(
% 2.31/0.66    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 2.31/0.66    inference(ennf_transformation,[],[f5])).
% 2.31/0.66  fof(f5,axiom,(
% 2.31/0.66    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 2.31/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 2.31/0.66  fof(f370,plain,(
% 2.31/0.66    ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | m1_subset_1(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) | (~spl7_21 | ~spl7_24)),
% 2.31/0.66    inference(subsumption_resolution,[],[f369,f239])).
% 2.31/0.66  fof(f369,plain,(
% 2.31/0.66    ~v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | m1_subset_1(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_zfmisc_1(u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))) | ~spl7_21),
% 2.31/0.66    inference(resolution,[],[f221,f55])).
% 2.31/0.66  fof(f55,plain,(
% 2.31/0.66    ( ! [X2,X0,X1] : (~m1_connsp_2(X2,X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 2.31/0.66    inference(cnf_transformation,[],[f23])).
% 2.31/0.66  fof(f23,plain,(
% 2.31/0.66    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.31/0.66    inference(flattening,[],[f22])).
% 2.31/0.66  fof(f22,plain,(
% 2.31/0.66    ! [X0,X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_connsp_2(X2,X0,X1)) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.31/0.66    inference(ennf_transformation,[],[f6])).
% 2.31/0.66  fof(f6,axiom,(
% 2.31/0.66    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X2] : (m1_connsp_2(X2,X0,X1) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))))),
% 2.31/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_connsp_2)).
% 2.31/0.66  fof(f406,plain,(
% 2.31/0.66    spl7_23 | ~spl7_5 | ~spl7_28),
% 2.31/0.66    inference(avatar_split_clause,[],[f352,f254,f88,f226])).
% 2.31/0.66  fof(f256,plain,(
% 2.31/0.66    spl7_28 | spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_7),
% 2.31/0.66    inference(avatar_split_clause,[],[f202,f96,f92,f88,f80,f76,f72,f254])).
% 2.31/0.66  fof(f202,plain,(
% 2.31/0.66    m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | (spl7_1 | spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 2.31/0.66    inference(subsumption_resolution,[],[f200,f73])).
% 2.31/0.66  fof(f200,plain,(
% 2.31/0.66    v2_struct_0(sK2) | m1_pre_topc(k1_tsep_1(sK0,sK1,sK2),sK0) | (spl7_2 | spl7_3 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 2.31/0.66    inference(resolution,[],[f137,f93])).
% 2.31/0.66  fof(f137,plain,(
% 2.31/0.66    ( ! [X3] : (~m1_pre_topc(X3,sK0) | v2_struct_0(X3) | m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK0)) ) | (spl7_2 | spl7_3 | ~spl7_5 | ~spl7_7)),
% 2.31/0.66    inference(subsumption_resolution,[],[f136,f81])).
% 2.31/0.66  fof(f136,plain,(
% 2.31/0.66    ( ! [X3] : (v2_struct_0(sK0) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK0) | m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK0)) ) | (spl7_2 | ~spl7_5 | ~spl7_7)),
% 2.31/0.66    inference(subsumption_resolution,[],[f135,f77])).
% 2.31/0.66  fof(f135,plain,(
% 2.31/0.66    ( ! [X3] : (v2_struct_0(sK1) | v2_struct_0(sK0) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK0) | m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK0)) ) | (~spl7_5 | ~spl7_7)),
% 2.31/0.66    inference(subsumption_resolution,[],[f124,f89])).
% 2.31/0.66  fof(f124,plain,(
% 2.31/0.66    ( ! [X3] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | v2_struct_0(X3) | ~m1_pre_topc(X3,sK0) | m1_pre_topc(k1_tsep_1(sK0,sK1,X3),sK0)) ) | ~spl7_7),
% 2.31/0.66    inference(resolution,[],[f97,f59])).
% 2.31/0.66  fof(f59,plain,(
% 2.31/0.66    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | m1_pre_topc(k1_tsep_1(X0,X1,X2),X0)) )),
% 2.31/0.66    inference(cnf_transformation,[],[f27])).
% 2.31/0.66  fof(f240,plain,(
% 2.31/0.66    spl7_24 | spl7_1 | spl7_2 | spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7),
% 2.31/0.66    inference(avatar_split_clause,[],[f185,f96,f92,f88,f84,f80,f76,f72,f238])).
% 2.31/0.66  fof(f84,plain,(
% 2.31/0.66    spl7_4 <=> v2_pre_topc(sK0)),
% 2.31/0.66    introduced(avatar_definition,[new_symbols(naming,[spl7_4])])).
% 2.31/0.66  fof(f185,plain,(
% 2.31/0.66    v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | (spl7_1 | spl7_2 | spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 2.31/0.66    inference(subsumption_resolution,[],[f183,f73])).
% 2.31/0.66  fof(f183,plain,(
% 2.31/0.66    v2_struct_0(sK2) | v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | (spl7_2 | spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 2.31/0.66    inference(resolution,[],[f134,f93])).
% 2.31/0.66  fof(f134,plain,(
% 2.31/0.66    ( ! [X1] : (~m1_pre_topc(X1,sK0) | v2_struct_0(X1) | v2_pre_topc(k1_tsep_1(sK0,sK1,X1))) ) | (spl7_2 | spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_7)),
% 2.31/0.66    inference(subsumption_resolution,[],[f133,f81])).
% 2.31/0.66  fof(f133,plain,(
% 2.31/0.66    ( ! [X1] : (v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_pre_topc(k1_tsep_1(sK0,sK1,X1))) ) | (spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_7)),
% 2.31/0.66    inference(subsumption_resolution,[],[f132,f77])).
% 2.31/0.66  fof(f132,plain,(
% 2.31/0.66    ( ! [X1] : (v2_struct_0(sK1) | v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_pre_topc(k1_tsep_1(sK0,sK1,X1))) ) | (~spl7_4 | ~spl7_5 | ~spl7_7)),
% 2.31/0.66    inference(subsumption_resolution,[],[f131,f89])).
% 2.31/0.66  fof(f131,plain,(
% 2.31/0.66    ( ! [X1] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_pre_topc(k1_tsep_1(sK0,sK1,X1))) ) | (~spl7_4 | ~spl7_7)),
% 2.31/0.66    inference(subsumption_resolution,[],[f122,f85])).
% 2.31/0.66  fof(f85,plain,(
% 2.31/0.66    v2_pre_topc(sK0) | ~spl7_4),
% 2.31/0.66    inference(avatar_component_clause,[],[f84])).
% 2.31/0.66  fof(f122,plain,(
% 2.31/0.66    ( ! [X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | v2_struct_0(X1) | ~m1_pre_topc(X1,sK0) | v2_pre_topc(k1_tsep_1(sK0,sK1,X1))) ) | ~spl7_7),
% 2.31/0.66    inference(resolution,[],[f97,f62])).
% 2.31/0.66  fof(f62,plain,(
% 2.31/0.66    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v2_pre_topc(k1_tsep_1(X0,X1,X2))) )),
% 2.31/0.66    inference(cnf_transformation,[],[f29])).
% 2.31/0.66  fof(f29,plain,(
% 2.31/0.66    ! [X0,X1,X2] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | ~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.31/0.66    inference(flattening,[],[f28])).
% 2.31/0.66  fof(f28,plain,(
% 2.31/0.66    ! [X0,X1,X2] : ((v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))) | (~m1_pre_topc(X2,X0) | v2_struct_0(X2) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.31/0.66    inference(ennf_transformation,[],[f11])).
% 2.31/0.66  fof(f11,axiom,(
% 2.31/0.66    ! [X0,X1,X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k1_tsep_1(X0,X1,X2)) & v1_pre_topc(k1_tsep_1(X0,X1,X2)) & ~v2_struct_0(k1_tsep_1(X0,X1,X2))))),
% 2.31/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tmap_1)).
% 2.31/0.66  fof(f228,plain,(
% 2.31/0.66    spl7_21 | spl7_22 | ~spl7_23 | spl7_1 | spl7_2 | spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_12),
% 2.31/0.66    inference(avatar_split_clause,[],[f186,f158,f96,f92,f88,f84,f80,f76,f72,f226,f223,f220])).
% 2.31/0.66  fof(f186,plain,(
% 2.31/0.66    ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | m1_connsp_2(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_tsep_1(sK0,sK1,sK2),sK3) | (spl7_1 | spl7_2 | spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7 | ~spl7_12)),
% 2.31/0.66    inference(subsumption_resolution,[],[f161,f185])).
% 2.31/0.66  fof(f161,plain,(
% 2.31/0.66    ~v2_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | ~l1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | v2_struct_0(k1_tsep_1(sK0,sK1,sK2)) | m1_connsp_2(sK6(k1_tsep_1(sK0,sK1,sK2),sK3),k1_tsep_1(sK0,sK1,sK2),sK3) | ~spl7_12),
% 2.31/0.66    inference(resolution,[],[f159,f54])).
% 2.31/0.66  fof(f54,plain,(
% 2.31/0.66    ( ! [X0,X1] : (~m1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_connsp_2(sK6(X0,X1),X0,X1)) )),
% 2.31/0.66    inference(cnf_transformation,[],[f21])).
% 2.31/0.66  fof(f21,plain,(
% 2.31/0.66    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | ~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.31/0.66    inference(flattening,[],[f20])).
% 2.31/0.66  fof(f20,plain,(
% 2.31/0.66    ! [X0,X1] : (? [X2] : m1_connsp_2(X2,X0,X1) | (~m1_subset_1(X1,u1_struct_0(X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.31/0.66    inference(ennf_transformation,[],[f7])).
% 2.31/0.66  fof(f7,axiom,(
% 2.31/0.66    ! [X0,X1] : ((m1_subset_1(X1,u1_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ? [X2] : m1_connsp_2(X2,X0,X1))),
% 2.31/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',existence_m1_connsp_2)).
% 2.31/0.66  fof(f214,plain,(
% 2.31/0.66    spl7_19 | spl7_1 | spl7_2 | spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7),
% 2.31/0.66    inference(avatar_split_clause,[],[f177,f96,f92,f88,f84,f80,f76,f72,f212])).
% 2.31/0.66  fof(f177,plain,(
% 2.31/0.66    v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | (spl7_1 | spl7_2 | spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 2.31/0.66    inference(subsumption_resolution,[],[f175,f73])).
% 2.31/0.66  fof(f175,plain,(
% 2.31/0.66    v2_struct_0(sK2) | v1_pre_topc(k1_tsep_1(sK0,sK1,sK2)) | (spl7_2 | spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_6 | ~spl7_7)),
% 2.31/0.66    inference(resolution,[],[f130,f93])).
% 2.31/0.66  fof(f130,plain,(
% 2.31/0.66    ( ! [X0] : (~m1_pre_topc(X0,sK0) | v2_struct_0(X0) | v1_pre_topc(k1_tsep_1(sK0,sK1,X0))) ) | (spl7_2 | spl7_3 | ~spl7_4 | ~spl7_5 | ~spl7_7)),
% 2.31/0.66    inference(subsumption_resolution,[],[f129,f81])).
% 2.31/0.66  fof(f129,plain,(
% 2.31/0.66    ( ! [X0] : (v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v1_pre_topc(k1_tsep_1(sK0,sK1,X0))) ) | (spl7_2 | ~spl7_4 | ~spl7_5 | ~spl7_7)),
% 2.31/0.66    inference(subsumption_resolution,[],[f128,f77])).
% 2.31/0.66  fof(f128,plain,(
% 2.31/0.66    ( ! [X0] : (v2_struct_0(sK1) | v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v1_pre_topc(k1_tsep_1(sK0,sK1,X0))) ) | (~spl7_4 | ~spl7_5 | ~spl7_7)),
% 2.31/0.66    inference(subsumption_resolution,[],[f127,f89])).
% 2.31/0.66  fof(f127,plain,(
% 2.31/0.66    ( ! [X0] : (~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v1_pre_topc(k1_tsep_1(sK0,sK1,X0))) ) | (~spl7_4 | ~spl7_7)),
% 2.31/0.66    inference(subsumption_resolution,[],[f121,f85])).
% 2.31/0.66  fof(f121,plain,(
% 2.31/0.66    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | v2_struct_0(X0) | ~m1_pre_topc(X0,sK0) | v1_pre_topc(k1_tsep_1(sK0,sK1,X0))) ) | ~spl7_7),
% 2.31/0.66    inference(resolution,[],[f97,f61])).
% 2.31/0.66  fof(f61,plain,(
% 2.31/0.66    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | v2_struct_0(X2) | ~m1_pre_topc(X2,X0) | v1_pre_topc(k1_tsep_1(X0,X1,X2))) )),
% 2.31/0.66    inference(cnf_transformation,[],[f29])).
% 2.31/0.66  fof(f210,plain,(
% 2.31/0.66    spl7_17 | spl7_18 | ~spl7_12),
% 2.31/0.66    inference(avatar_split_clause,[],[f162,f158,f208,f205])).
% 2.31/0.66  fof(f162,plain,(
% 2.31/0.66    v1_xboole_0(u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | r2_hidden(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2))) | ~spl7_12),
% 2.31/0.66    inference(resolution,[],[f159,f65])).
% 2.31/0.66  fof(f65,plain,(
% 2.31/0.66    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 2.31/0.66    inference(cnf_transformation,[],[f33])).
% 2.31/0.66  fof(f33,plain,(
% 2.31/0.66    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 2.31/0.66    inference(flattening,[],[f32])).
% 2.31/0.66  fof(f32,plain,(
% 2.31/0.66    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 2.31/0.66    inference(ennf_transformation,[],[f3])).
% 2.31/0.66  fof(f3,axiom,(
% 2.31/0.66    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 2.31/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 2.31/0.66  fof(f160,plain,(
% 2.31/0.66    spl7_12),
% 2.31/0.66    inference(avatar_split_clause,[],[f36,f158])).
% 2.31/0.66  fof(f36,plain,(
% 2.31/0.66    m1_subset_1(sK3,u1_struct_0(k1_tsep_1(sK0,sK1,sK2)))),
% 2.31/0.66    inference(cnf_transformation,[],[f16])).
% 2.31/0.66  fof(f16,plain,(
% 2.31/0.66    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.31/0.66    inference(flattening,[],[f15])).
% 2.31/0.66  fof(f15,plain,(
% 2.31/0.66    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((! [X4] : (X3 != X4 | ~m1_subset_1(X4,u1_struct_0(X2))) & ! [X5] : (X3 != X5 | ~m1_subset_1(X5,u1_struct_0(X1)))) & m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2)))) & (m1_pre_topc(X2,X0) & ~v2_struct_0(X2))) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.31/0.66    inference(ennf_transformation,[],[f14])).
% 2.31/0.66  fof(f14,plain,(
% 2.31/0.66    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X5] : (m1_subset_1(X5,u1_struct_0(X1)) => X3 != X5))))))),
% 2.31/0.66    inference(rectify,[],[f13])).
% 2.31/0.66  fof(f13,negated_conjecture,(
% 2.31/0.66    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => X3 != X4))))))),
% 2.31/0.66    inference(negated_conjecture,[],[f12])).
% 2.31/0.66  fof(f12,conjecture,(
% 2.31/0.66    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : ((m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) => ! [X3] : (m1_subset_1(X3,u1_struct_0(k1_tsep_1(X0,X1,X2))) => ~(! [X4] : (m1_subset_1(X4,u1_struct_0(X2)) => X3 != X4) & ! [X4] : (m1_subset_1(X4,u1_struct_0(X1)) => X3 != X4))))))),
% 2.31/0.66    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_tmap_1)).
% 2.31/0.66  fof(f156,plain,(
% 2.31/0.66    ~spl7_11),
% 2.31/0.66    inference(avatar_split_clause,[],[f67,f154])).
% 2.31/0.66  fof(f67,plain,(
% 2.31/0.66    ~m1_subset_1(sK3,u1_struct_0(sK2))),
% 2.31/0.66    inference(equality_resolution,[],[f34])).
% 2.31/0.66  fof(f34,plain,(
% 2.31/0.66    ( ! [X4] : (~m1_subset_1(X4,u1_struct_0(sK2)) | sK3 != X4) )),
% 2.31/0.66    inference(cnf_transformation,[],[f16])).
% 2.31/0.66  fof(f148,plain,(
% 2.31/0.66    ~spl7_9),
% 2.31/0.66    inference(avatar_split_clause,[],[f66,f146])).
% 2.31/0.66  fof(f66,plain,(
% 2.31/0.66    ~m1_subset_1(sK3,u1_struct_0(sK1))),
% 2.31/0.66    inference(equality_resolution,[],[f35])).
% 2.31/0.66  fof(f35,plain,(
% 2.31/0.66    ( ! [X5] : (~m1_subset_1(X5,u1_struct_0(sK1)) | sK3 != X5) )),
% 2.31/0.66    inference(cnf_transformation,[],[f16])).
% 2.31/0.66  fof(f98,plain,(
% 2.31/0.66    spl7_7),
% 2.31/0.66    inference(avatar_split_clause,[],[f40,f96])).
% 2.31/0.66  fof(f40,plain,(
% 2.31/0.66    m1_pre_topc(sK1,sK0)),
% 2.31/0.66    inference(cnf_transformation,[],[f16])).
% 2.31/0.66  fof(f94,plain,(
% 2.31/0.66    spl7_6),
% 2.31/0.66    inference(avatar_split_clause,[],[f38,f92])).
% 2.31/0.66  fof(f38,plain,(
% 2.31/0.66    m1_pre_topc(sK2,sK0)),
% 2.31/0.66    inference(cnf_transformation,[],[f16])).
% 2.31/0.66  fof(f90,plain,(
% 2.31/0.66    spl7_5),
% 2.31/0.66    inference(avatar_split_clause,[],[f43,f88])).
% 2.31/0.66  fof(f43,plain,(
% 2.31/0.66    l1_pre_topc(sK0)),
% 2.31/0.66    inference(cnf_transformation,[],[f16])).
% 2.31/0.66  fof(f86,plain,(
% 2.31/0.66    spl7_4),
% 2.31/0.66    inference(avatar_split_clause,[],[f42,f84])).
% 2.31/0.66  fof(f42,plain,(
% 2.31/0.66    v2_pre_topc(sK0)),
% 2.31/0.66    inference(cnf_transformation,[],[f16])).
% 2.31/0.66  fof(f82,plain,(
% 2.31/0.66    ~spl7_3),
% 2.31/0.66    inference(avatar_split_clause,[],[f41,f80])).
% 2.31/0.66  fof(f41,plain,(
% 2.31/0.66    ~v2_struct_0(sK0)),
% 2.31/0.66    inference(cnf_transformation,[],[f16])).
% 2.31/0.66  fof(f78,plain,(
% 2.31/0.66    ~spl7_2),
% 2.31/0.66    inference(avatar_split_clause,[],[f39,f76])).
% 2.31/0.66  fof(f39,plain,(
% 2.31/0.66    ~v2_struct_0(sK1)),
% 2.31/0.66    inference(cnf_transformation,[],[f16])).
% 2.31/0.66  fof(f74,plain,(
% 2.31/0.66    ~spl7_1),
% 2.31/0.66    inference(avatar_split_clause,[],[f37,f72])).
% 2.31/0.66  fof(f37,plain,(
% 2.31/0.66    ~v2_struct_0(sK2)),
% 2.31/0.66    inference(cnf_transformation,[],[f16])).
% 2.31/0.66  % SZS output end Proof for theBenchmark
% 2.31/0.66  % (24378)------------------------------
% 2.31/0.66  % (24378)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.31/0.66  % (24378)Termination reason: Refutation
% 2.31/0.66  
% 2.31/0.66  % (24378)Memory used [KB]: 8059
% 2.31/0.66  % (24378)Time elapsed: 0.200 s
% 2.31/0.66  % (24378)------------------------------
% 2.31/0.66  % (24378)------------------------------
% 2.31/0.67  % (24377)Success in time 0.291 s
%------------------------------------------------------------------------------
