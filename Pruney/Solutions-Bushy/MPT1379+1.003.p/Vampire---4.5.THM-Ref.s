%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1379+1.003 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n029.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:49:50 EST 2020

% Result     : Theorem 2.18s
% Output     : Refutation 2.18s
% Verified   : 
% Statistics : Number of formulae       :  172 ( 431 expanded)
%              Number of leaves         :   26 ( 177 expanded)
%              Depth                    :   12
%              Number of atoms          :  664 (1509 expanded)
%              Number of equality atoms :   34 (  76 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3064,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f57,f61,f65,f69,f73,f77,f109,f116,f121,f140,f148,f198,f594,f744,f1226,f2952,f2968,f2976,f2995,f3018,f3021,f3029,f3059,f3061,f3063])).

fof(f3063,plain,
    ( spl6_50
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f3062,f138,f71,f67,f63,f59,f55,f2974])).

fof(f2974,plain,
    ( spl6_50
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_50])])).

fof(f55,plain,
    ( spl6_1
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f59,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f63,plain,
    ( spl6_3
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f67,plain,
    ( spl6_4
  <=> m1_subset_1(sK1,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f71,plain,
    ( spl6_5
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f138,plain,
    ( spl6_11
  <=> m1_connsp_2(sK3,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f3062,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_11 ),
    inference(subsumption_resolution,[],[f3022,f68])).

fof(f68,plain,
    ( m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f3022,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_11 ),
    inference(resolution,[],[f139,f87])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK3,sK0,X0)
        | r2_hidden(X0,k1_tops_1(sK0,sK3))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f86,f56])).

fof(f56,plain,
    ( ~ v2_struct_0(sK0)
    | spl6_1 ),
    inference(avatar_component_clause,[],[f55])).

fof(f86,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X0,k1_tops_1(sK0,sK3))
        | ~ m1_connsp_2(sK3,sK0,X0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f85,f64])).

fof(f64,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f63])).

fof(f85,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X0,k1_tops_1(sK0,sK3))
        | ~ m1_connsp_2(sK3,sK0,X0) )
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f79,f60])).

fof(f60,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f59])).

fof(f79,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X0,k1_tops_1(sK0,sK3))
        | ~ m1_connsp_2(sK3,sK0,X0) )
    | ~ spl6_5 ),
    inference(resolution,[],[f72,f41])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0)
      | r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( m1_connsp_2(X2,X0,X1)
              <=> r2_hidden(X1,k1_tops_1(X0,X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_connsp_2)).

fof(f72,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f139,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f138])).

fof(f3061,plain,
    ( spl6_49
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f3060,f111,f75,f67,f63,f59,f55,f2966])).

fof(f2966,plain,
    ( spl6_49
  <=> r2_hidden(sK1,k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_49])])).

fof(f75,plain,
    ( spl6_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f111,plain,
    ( spl6_8
  <=> m1_connsp_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f3060,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(subsumption_resolution,[],[f2996,f68])).

fof(f2996,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_8 ),
    inference(resolution,[],[f112,f101])).

fof(f101,plain,
    ( ! [X0] :
        ( ~ m1_connsp_2(sK2,sK0,X0)
        | r2_hidden(X0,k1_tops_1(sK0,sK2))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f100,f56])).

fof(f100,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X0,k1_tops_1(sK0,sK2))
        | ~ m1_connsp_2(sK2,sK0,X0) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f99,f64])).

fof(f99,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X0,k1_tops_1(sK0,sK2))
        | ~ m1_connsp_2(sK2,sK0,X0) )
    | ~ spl6_2
    | ~ spl6_6 ),
    inference(subsumption_resolution,[],[f93,f60])).

fof(f93,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X0,k1_tops_1(sK0,sK2))
        | ~ m1_connsp_2(sK2,sK0,X0) )
    | ~ spl6_6 ),
    inference(resolution,[],[f76,f41])).

fof(f76,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f75])).

fof(f112,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f111])).

fof(f3059,plain,
    ( spl6_48
    | ~ spl6_49
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f3056,f2974,f2966,f2950])).

fof(f2950,plain,
    ( spl6_48
  <=> sP5(sK1,k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f3056,plain,
    ( sP5(sK1,k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
    | ~ spl6_49
    | ~ spl6_50 ),
    inference(resolution,[],[f2987,f2975])).

fof(f2975,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ spl6_50 ),
    inference(avatar_component_clause,[],[f2974])).

fof(f2987,plain,
    ( ! [X1] :
        ( ~ r2_hidden(sK1,X1)
        | sP5(sK1,X1,k1_tops_1(sK0,sK2)) )
    | ~ spl6_49 ),
    inference(resolution,[],[f2967,f43])).

fof(f43,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,X0)
      | ~ r2_hidden(X3,X1)
      | sP5(X3,X1,X0) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X0,X1) = X2
    <=> ! [X3] :
          ( r2_hidden(X3,X2)
        <=> ( r2_hidden(X3,X1)
            & r2_hidden(X3,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

fof(f2967,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl6_49 ),
    inference(avatar_component_clause,[],[f2966])).

fof(f3029,plain,
    ( spl6_22
    | ~ spl6_32
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f2960,f2950,f1224,f742])).

fof(f742,plain,
    ( spl6_22
  <=> r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f1224,plain,
    ( spl6_32
  <=> k1_tops_1(sK0,k3_xboole_0(sK2,sK3)) = k3_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_32])])).

fof(f2960,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | ~ spl6_32
    | ~ spl6_48 ),
    inference(forward_demodulation,[],[f2959,f1225])).

fof(f1225,plain,
    ( k1_tops_1(sK0,k3_xboole_0(sK2,sK3)) = k3_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3))
    | ~ spl6_32 ),
    inference(avatar_component_clause,[],[f1224])).

fof(f2959,plain,
    ( r2_hidden(sK1,k3_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3)))
    | ~ spl6_48 ),
    inference(resolution,[],[f2951,f53])).

fof(f53,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,k3_xboole_0(X0,X1)) ) ),
    inference(equality_resolution,[],[f46])).

fof(f46,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f2951,plain,
    ( sP5(sK1,k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f2950])).

fof(f3021,plain,
    ( spl6_11
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_50 ),
    inference(avatar_split_clause,[],[f3006,f2974,f71,f67,f63,f59,f55,f138])).

fof(f3006,plain,
    ( m1_connsp_2(sK3,sK0,sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f3005,f56])).

fof(f3005,plain,
    ( v2_struct_0(sK0)
    | m1_connsp_2(sK3,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f3004,f72])).

fof(f3004,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK3,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f3003,f68])).

fof(f3003,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK3,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f3002,f64])).

fof(f3002,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK3,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_50 ),
    inference(subsumption_resolution,[],[f2999,f60])).

fof(f2999,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK3,sK0,sK1)
    | ~ spl6_50 ),
    inference(resolution,[],[f2975,f40])).

fof(f40,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X1,k1_tops_1(X0,X2))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | m1_connsp_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3018,plain,
    ( spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_9
    | ~ spl6_22 ),
    inference(avatar_contradiction_clause,[],[f3017])).

fof(f3017,plain,
    ( $false
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | spl6_9
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f3016,f3009])).

fof(f3009,plain,
    ( ~ m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl6_5
    | spl6_9 ),
    inference(forward_demodulation,[],[f147,f81])).

fof(f81,plain,
    ( ! [X2] : k9_subset_1(u1_struct_0(sK0),X2,sK3) = k3_xboole_0(X2,sK3)
    | ~ spl6_5 ),
    inference(resolution,[],[f72,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f147,plain,
    ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | spl6_9 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl6_9
  <=> m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f3016,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f3015,f56])).

fof(f3015,plain,
    ( v2_struct_0(sK0)
    | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f3014,f90])).

fof(f90,plain,
    ( ! [X3] : m1_subset_1(k3_xboole_0(X3,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f82,f81])).

fof(f82,plain,
    ( ! [X3] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X3,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_5 ),
    inference(resolution,[],[f72,f37])).

fof(f37,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f3014,plain,
    ( ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f3013,f68])).

fof(f3013,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f3012,f64])).

fof(f3012,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl6_2
    | ~ spl6_22 ),
    inference(subsumption_resolution,[],[f746,f60])).

fof(f746,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(k3_xboole_0(sK2,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl6_22 ),
    inference(resolution,[],[f743,f40])).

fof(f743,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | ~ spl6_22 ),
    inference(avatar_component_clause,[],[f742])).

fof(f2995,plain,
    ( spl6_8
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_49 ),
    inference(avatar_split_clause,[],[f2992,f2966,f75,f67,f63,f59,f55,f111])).

fof(f2992,plain,
    ( m1_connsp_2(sK2,sK0,sK1)
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_49 ),
    inference(subsumption_resolution,[],[f2991,f56])).

fof(f2991,plain,
    ( v2_struct_0(sK0)
    | m1_connsp_2(sK2,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_49 ),
    inference(subsumption_resolution,[],[f2990,f76])).

fof(f2990,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK2,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_49 ),
    inference(subsumption_resolution,[],[f2989,f68])).

fof(f2989,plain,
    ( ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK2,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_49 ),
    inference(subsumption_resolution,[],[f2988,f64])).

fof(f2988,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK2,sK0,sK1)
    | ~ spl6_2
    | ~ spl6_49 ),
    inference(subsumption_resolution,[],[f2985,f60])).

fof(f2985,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | m1_connsp_2(sK2,sK0,sK1)
    | ~ spl6_49 ),
    inference(resolution,[],[f2967,f40])).

fof(f2976,plain,
    ( spl6_50
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f2958,f2950,f2974])).

fof(f2958,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK3))
    | ~ spl6_48 ),
    inference(resolution,[],[f2951,f45])).

fof(f45,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f2968,plain,
    ( spl6_49
    | ~ spl6_48 ),
    inference(avatar_split_clause,[],[f2957,f2950,f2966])).

fof(f2957,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,sK2))
    | ~ spl6_48 ),
    inference(resolution,[],[f2951,f44])).

fof(f44,plain,(
    ! [X0,X3,X1] :
      ( ~ sP5(X3,X1,X0)
      | r2_hidden(X3,X0) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f2952,plain,
    ( spl6_48
    | ~ spl6_22
    | ~ spl6_32 ),
    inference(avatar_split_clause,[],[f2944,f1224,f742,f2950])).

fof(f2944,plain,
    ( sP5(sK1,k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2))
    | ~ spl6_22
    | ~ spl6_32 ),
    inference(resolution,[],[f1242,f743])).

fof(f1242,plain,
    ( ! [X1] :
        ( ~ r2_hidden(X1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
        | sP5(X1,k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) )
    | ~ spl6_32 ),
    inference(superposition,[],[f52,f1225])).

fof(f52,plain,(
    ! [X0,X3,X1] :
      ( ~ r2_hidden(X3,k3_xboole_0(X0,X1))
      | sP5(X3,X1,X0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X3,X1] :
      ( sP5(X3,X1,X0)
      | ~ r2_hidden(X3,X2)
      | k3_xboole_0(X0,X1) != X2 ) ),
    inference(cnf_transformation,[],[f3])).

fof(f1226,plain,
    ( spl6_32
    | ~ spl6_7
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f679,f592,f107,f1224])).

fof(f107,plain,
    ( spl6_7
  <=> m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f592,plain,
    ( spl6_16
  <=> k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,k3_xboole_0(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f679,plain,
    ( k1_tops_1(sK0,k3_xboole_0(sK2,sK3)) = k3_xboole_0(k1_tops_1(sK0,sK2),k1_tops_1(sK0,sK3))
    | ~ spl6_7
    | ~ spl6_16 ),
    inference(superposition,[],[f593,f176])).

fof(f176,plain,
    ( ! [X4] : k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),X4) = k3_xboole_0(X4,k1_tops_1(sK0,sK3))
    | ~ spl6_7 ),
    inference(forward_demodulation,[],[f168,f166])).

fof(f166,plain,
    ( ! [X2] : k9_subset_1(u1_struct_0(sK0),X2,k1_tops_1(sK0,sK3)) = k3_xboole_0(X2,k1_tops_1(sK0,sK3))
    | ~ spl6_7 ),
    inference(resolution,[],[f108,f50])).

fof(f108,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f107])).

fof(f168,plain,
    ( ! [X4] : k9_subset_1(u1_struct_0(sK0),X4,k1_tops_1(sK0,sK3)) = k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),X4)
    | ~ spl6_7 ),
    inference(resolution,[],[f108,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k9_subset_1(X0,X2,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k9_subset_1)).

fof(f593,plain,
    ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,k3_xboole_0(sK2,sK3))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f592])).

fof(f744,plain,
    ( spl6_22
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f740,f119,f71,f67,f63,f59,f55,f742])).

fof(f119,plain,
    ( spl6_10
  <=> m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f740,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_5
    | ~ spl6_10 ),
    inference(subsumption_resolution,[],[f739,f68])).

fof(f739,plain,
    ( r2_hidden(sK1,k1_tops_1(sK0,k3_xboole_0(sK2,sK3)))
    | ~ m1_subset_1(sK1,u1_struct_0(sK0))
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_10 ),
    inference(resolution,[],[f132,f120])).

fof(f120,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f119])).

fof(f132,plain,
    ( ! [X2,X1] :
        ( ~ m1_connsp_2(k3_xboole_0(X2,sK3),sK0,X1)
        | r2_hidden(X1,k1_tops_1(sK0,k3_xboole_0(X2,sK3)))
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f131,f56])).

fof(f131,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X1,k1_tops_1(sK0,k3_xboole_0(X2,sK3)))
        | ~ m1_connsp_2(k3_xboole_0(X2,sK3),sK0,X1) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f130,f64])).

fof(f130,plain,
    ( ! [X2,X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X1,k1_tops_1(sK0,k3_xboole_0(X2,sK3)))
        | ~ m1_connsp_2(k3_xboole_0(X2,sK3),sK0,X1) )
    | ~ spl6_2
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f124,f60])).

fof(f124,plain,
    ( ! [X2,X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ l1_pre_topc(sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_struct_0(sK0)
        | r2_hidden(X1,k1_tops_1(sK0,k3_xboole_0(X2,sK3)))
        | ~ m1_connsp_2(k3_xboole_0(X2,sK3),sK0,X1) )
    | ~ spl6_5 ),
    inference(resolution,[],[f90,f41])).

fof(f594,plain,
    ( spl6_16
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_13 ),
    inference(avatar_split_clause,[],[f228,f196,f75,f71,f63,f59,f592])).

fof(f196,plain,
    ( spl6_13
  <=> k3_xboole_0(sK2,sK3) = k3_xboole_0(sK3,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f228,plain,
    ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,k3_xboole_0(sK2,sK3))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6
    | ~ spl6_13 ),
    inference(forward_demodulation,[],[f227,f197])).

fof(f197,plain,
    ( k3_xboole_0(sK2,sK3) = k3_xboole_0(sK3,sK2)
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f196])).

fof(f227,plain,
    ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,k3_xboole_0(sK3,sK2))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f220,f95])).

fof(f95,plain,
    ( ! [X2] : k9_subset_1(u1_struct_0(sK0),X2,sK2) = k3_xboole_0(X2,sK2)
    | ~ spl6_6 ),
    inference(resolution,[],[f76,f50])).

fof(f220,plain,
    ( k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,sK2)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK3,sK2))
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(resolution,[],[f89,f76])).

fof(f89,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,X1)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK3,X1)) )
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f88,f60])).

fof(f88,plain,
    ( ! [X1] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,X1)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK3,X1)) )
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f80,f64])).

fof(f80,plain,
    ( ! [X1] :
        ( ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k9_subset_1(u1_struct_0(sK0),k1_tops_1(sK0,sK3),k1_tops_1(sK0,X1)) = k1_tops_1(sK0,k9_subset_1(u1_struct_0(sK0),sK3,X1)) )
    | ~ spl6_5 ),
    inference(resolution,[],[f72,f38])).

fof(f38,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => k9_subset_1(u1_struct_0(X0),k1_tops_1(X0,X1),k1_tops_1(X0,X2)) = k1_tops_1(X0,k9_subset_1(u1_struct_0(X0),X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tops_1)).

fof(f198,plain,
    ( spl6_13
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f191,f75,f71,f196])).

fof(f191,plain,
    ( k3_xboole_0(sK2,sK3) = k3_xboole_0(sK3,sK2)
    | ~ spl6_5
    | ~ spl6_6 ),
    inference(superposition,[],[f95,f91])).

fof(f91,plain,
    ( ! [X4] : k9_subset_1(u1_struct_0(sK0),sK3,X4) = k3_xboole_0(X4,sK3)
    | ~ spl6_5 ),
    inference(forward_demodulation,[],[f83,f81])).

fof(f83,plain,
    ( ! [X4] : k9_subset_1(u1_struct_0(sK0),X4,sK3) = k9_subset_1(u1_struct_0(sK0),sK3,X4)
    | ~ spl6_5 ),
    inference(resolution,[],[f72,f36])).

fof(f148,plain,
    ( ~ spl6_11
    | ~ spl6_8
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f27,f114,f111,f138])).

fof(f27,plain,
    ( ~ m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | ~ m1_connsp_2(sK2,sK0,sK1)
    | ~ m1_connsp_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                  <~> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                  <~> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) )
                  & m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,u1_struct_0(X0)) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,u1_struct_0(X0))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => ( ( m1_connsp_2(X3,X0,X1)
                        & m1_connsp_2(X2,X0,X1) )
                    <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( m1_connsp_2(X3,X0,X1)
                      & m1_connsp_2(X2,X0,X1) )
                  <=> m1_connsp_2(k9_subset_1(u1_struct_0(X0),X2,X3),X0,X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_connsp_2)).

fof(f140,plain,
    ( spl6_11
    | spl6_9 ),
    inference(avatar_split_clause,[],[f29,f114,f138])).

fof(f29,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | m1_connsp_2(sK3,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f121,plain,
    ( spl6_10
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f117,f114,f71,f119])).

fof(f117,plain,
    ( m1_connsp_2(k3_xboole_0(sK2,sK3),sK0,sK1)
    | ~ spl6_5
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f115,f81])).

fof(f115,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f114])).

fof(f116,plain,
    ( spl6_8
    | spl6_9 ),
    inference(avatar_split_clause,[],[f28,f114,f111])).

fof(f28,plain,
    ( m1_connsp_2(k9_subset_1(u1_struct_0(sK0),sK2,sK3),sK0,sK1)
    | m1_connsp_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f109,plain,
    ( spl6_7
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(avatar_split_clause,[],[f84,f71,f63,f107])).

fof(f84,plain,
    ( m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_3
    | ~ spl6_5 ),
    inference(subsumption_resolution,[],[f78,f64])).

fof(f78,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(k1_tops_1(sK0,sK3),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_5 ),
    inference(resolution,[],[f72,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k1_tops_1(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tops_1)).

fof(f77,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f31,f75])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f73,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f30,f71])).

fof(f30,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f69,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f32,f67])).

fof(f32,plain,(
    m1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f65,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f35,f63])).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f61,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f34,f59])).

fof(f34,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f57,plain,(
    ~ spl6_1 ),
    inference(avatar_split_clause,[],[f33,f55])).

fof(f33,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

%------------------------------------------------------------------------------
