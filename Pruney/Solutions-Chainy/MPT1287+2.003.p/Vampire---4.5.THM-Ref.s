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
% DateTime   : Thu Dec  3 13:13:08 EST 2020

% Result     : Theorem 1.41s
% Output     : Refutation 1.41s
% Verified   : 
% Statistics : Number of formulae       :  104 ( 228 expanded)
%              Number of leaves         :   28 ( 110 expanded)
%              Depth                    :    7
%              Number of atoms          :  315 ( 887 expanded)
%              Number of equality atoms :   22 (  30 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f478,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f44,f49,f54,f59,f64,f69,f74,f81,f86,f101,f109,f114,f340,f381,f397,f428,f446,f477])).

fof(f477,plain,
    ( ~ spl3_60
    | spl3_1
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f447,f66,f56,f41,f443])).

fof(f443,plain,
    ( spl3_60
  <=> v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f41,plain,
    ( spl3_1
  <=> v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f56,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f66,plain,
    ( spl3_6
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f447,plain,
    ( ~ v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0)
    | spl3_1
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f68,f43,f87,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v6_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v6_tops_1(X1,X0)
              | ~ v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v6_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v6_tops_1(X1,X0)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v6_tops_1(X1,X0)
          <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_tops_1)).

fof(f87,plain,
    ( ! [X0] : m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f58,f32])).

fof(f32,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).

fof(f58,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f56])).

fof(f43,plain,
    ( ~ v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f41])).

fof(f68,plain,
    ( l1_pre_topc(sK0)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f66])).

fof(f446,plain,
    ( spl3_60
    | ~ spl3_52
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f441,f418,f394,f443])).

fof(f394,plain,
    ( spl3_52
  <=> v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f418,plain,
    ( spl3_57
  <=> k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f441,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0)
    | ~ spl3_52
    | ~ spl3_57 ),
    inference(backward_demodulation,[],[f396,f420])).

fof(f420,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f418])).

fof(f396,plain,
    ( v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)),sK0)
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f394])).

fof(f428,plain,
    ( spl3_57
    | ~ spl3_42
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f427,f378,f337,f418])).

fof(f337,plain,
    ( spl3_42
  <=> k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f378,plain,
    ( spl3_49
  <=> k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f427,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))
    | ~ spl3_42
    | ~ spl3_49 ),
    inference(forward_demodulation,[],[f339,f380])).

fof(f380,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f378])).

fof(f339,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)))
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f337])).

fof(f397,plain,
    ( spl3_52
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f282,f111,f106,f83,f78,f71,f66,f394])).

fof(f71,plain,
    ( spl3_7
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f78,plain,
    ( spl3_8
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f83,plain,
    ( spl3_9
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f106,plain,
    ( spl3_12
  <=> v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f111,plain,
    ( spl3_13
  <=> v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f282,plain,
    ( v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)),sK0)
    | ~ spl3_6
    | ~ spl3_7
    | ~ spl3_8
    | ~ spl3_9
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(unit_resulting_resolution,[],[f73,f68,f108,f80,f113,f85,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v5_tops_1(X2,X0)
      | ~ v5_tops_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v5_tops_1(X2,X0)
              | ~ v5_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v5_tops_1(X2,X0)
              | ~ v5_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v5_tops_1(X2,X0)
                  & v5_tops_1(X1,X0) )
               => v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_tops_1)).

fof(f85,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f83])).

fof(f113,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f111])).

fof(f80,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f108,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f106])).

fof(f73,plain,
    ( v2_pre_topc(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f71])).

fof(f381,plain,
    ( spl3_49
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f376,f98,f83,f61,f378])).

fof(f61,plain,
    ( spl3_5
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f98,plain,
    ( spl3_11
  <=> sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f376,plain,
    ( k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f286,f100])).

fof(f100,plain,
    ( sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f98])).

fof(f286,plain,
    ( k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f63,f85,f33])).

fof(f33,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).

fof(f63,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f61])).

fof(f340,plain,
    ( spl3_42
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f294,f83,f61,f337])).

fof(f294,plain,
    ( k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)))
    | ~ spl3_5
    | ~ spl3_9 ),
    inference(unit_resulting_resolution,[],[f63,f85,f36])).

fof(f36,plain,(
    ! [X2,X0,X1] :
      ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).

fof(f114,plain,
    ( spl3_13
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f102,f66,f56,f46,f111])).

fof(f46,plain,
    ( spl3_2
  <=> v6_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f102,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f68,f48,f58,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ v6_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f48,plain,
    ( v6_tops_1(sK2,sK0)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f46])).

fof(f109,plain,
    ( spl3_12
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f103,f66,f61,f51,f106])).

fof(f51,plain,
    ( spl3_3
  <=> v6_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f103,plain,
    ( v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl3_3
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(unit_resulting_resolution,[],[f68,f53,f63,f34])).

fof(f53,plain,
    ( v6_tops_1(sK1,sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f51])).

fof(f101,plain,
    ( spl3_11
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f89,f56,f98])).

fof(f89,plain,
    ( sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f58,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f86,plain,
    ( spl3_9
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f75,f56,f83])).

fof(f75,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_4 ),
    inference(unit_resulting_resolution,[],[f58,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f81,plain,
    ( spl3_8
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f76,f61,f78])).

fof(f76,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl3_5 ),
    inference(unit_resulting_resolution,[],[f63,f38])).

fof(f74,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f25,f71])).

fof(f25,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,
    ( ~ v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v6_tops_1(sK2,sK0)
    & v6_tops_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f22,f21,f20])).

fof(f20,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v6_tops_1(X2,X0)
                & v6_tops_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v6_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v6_tops_1(X2,sK0)
              & v6_tops_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v6_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & v6_tops_1(X2,sK0)
            & v6_tops_1(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & v6_tops_1(X2,sK0)
          & v6_tops_1(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,
    ( ? [X2] :
        ( ~ v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & v6_tops_1(X2,sK0)
        & v6_tops_1(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & v6_tops_1(sK2,sK0)
      & v6_tops_1(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v6_tops_1(X2,X0)
              & v6_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v6_tops_1(X2,X0)
              & v6_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v6_tops_1(X2,X0)
                    & v6_tops_1(X1,X0) )
                 => v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v6_tops_1(X2,X0)
                  & v6_tops_1(X1,X0) )
               => v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_tops_1)).

fof(f69,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f26,f66])).

fof(f26,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f64,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f27,f61])).

fof(f27,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f59,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f28,f56])).

fof(f28,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f54,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f29,f51])).

fof(f29,plain,(
    v6_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f49,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f30,f46])).

fof(f30,plain,(
    v6_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f44,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f31,f41])).

fof(f31,plain,(
    ~ v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n014.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 11:53:37 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (1850)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.50  % (1851)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.50  % (1856)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.51  % (1852)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.51  % (1867)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.51  % (1848)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.51  % (1857)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.51  % (1870)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.51  % (1860)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.51  % (1849)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.51  % (1862)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.51  % (1866)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.51  % (1850)Refutation not found, incomplete strategy% (1850)------------------------------
% 0.22/0.51  % (1850)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.51  % (1850)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.51  
% 0.22/0.51  % (1850)Memory used [KB]: 10490
% 0.22/0.51  % (1850)Time elapsed: 0.093 s
% 0.22/0.51  % (1850)------------------------------
% 0.22/0.51  % (1850)------------------------------
% 0.22/0.52  % (1858)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.52  % (1859)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 0.22/0.52  % (1865)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.52  % (1868)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.52  % (1870)Refutation not found, incomplete strategy% (1870)------------------------------
% 0.22/0.52  % (1870)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (1870)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (1870)Memory used [KB]: 10618
% 0.22/0.52  % (1870)Time elapsed: 0.063 s
% 0.22/0.52  % (1870)------------------------------
% 0.22/0.52  % (1870)------------------------------
% 1.23/0.53  % (1855)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 1.23/0.53  % (1854)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.23/0.53  % (1853)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 1.23/0.53  % (1857)Refutation not found, incomplete strategy% (1857)------------------------------
% 1.23/0.53  % (1857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.23/0.53  % (1857)Termination reason: Refutation not found, incomplete strategy
% 1.23/0.53  
% 1.23/0.53  % (1857)Memory used [KB]: 10618
% 1.23/0.53  % (1857)Time elapsed: 0.107 s
% 1.23/0.53  % (1857)------------------------------
% 1.23/0.53  % (1857)------------------------------
% 1.23/0.53  % (1864)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 1.23/0.53  % (1847)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 1.23/0.54  % (1861)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 1.41/0.54  % (1853)Refutation found. Thanks to Tanya!
% 1.41/0.54  % SZS status Theorem for theBenchmark
% 1.41/0.54  % (1863)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 1.41/0.55  % (1869)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 1.41/0.55  % SZS output start Proof for theBenchmark
% 1.41/0.56  fof(f478,plain,(
% 1.41/0.56    $false),
% 1.41/0.56    inference(avatar_sat_refutation,[],[f44,f49,f54,f59,f64,f69,f74,f81,f86,f101,f109,f114,f340,f381,f397,f428,f446,f477])).
% 1.41/0.56  fof(f477,plain,(
% 1.41/0.56    ~spl3_60 | spl3_1 | ~spl3_4 | ~spl3_6),
% 1.41/0.56    inference(avatar_split_clause,[],[f447,f66,f56,f41,f443])).
% 1.41/0.56  fof(f443,plain,(
% 1.41/0.56    spl3_60 <=> v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0)),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 1.41/0.56  fof(f41,plain,(
% 1.41/0.56    spl3_1 <=> v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.41/0.56  fof(f56,plain,(
% 1.41/0.56    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.41/0.56  fof(f66,plain,(
% 1.41/0.56    spl3_6 <=> l1_pre_topc(sK0)),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.41/0.56  fof(f447,plain,(
% 1.41/0.56    ~v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0) | (spl3_1 | ~spl3_4 | ~spl3_6)),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f68,f43,f87,f35])).
% 1.41/0.56  fof(f35,plain,(
% 1.41/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v6_tops_1(X1,X0)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f24])).
% 1.41/0.56  fof(f24,plain,(
% 1.41/0.56    ! [X0] : (! [X1] : (((v6_tops_1(X1,X0) | ~v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) & (v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) | ~v6_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.41/0.56    inference(nnf_transformation,[],[f14])).
% 1.41/0.56  fof(f14,plain,(
% 1.41/0.56    ! [X0] : (! [X1] : ((v6_tops_1(X1,X0) <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.41/0.56    inference(ennf_transformation,[],[f6])).
% 1.41/0.56  fof(f6,axiom,(
% 1.41/0.56    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v6_tops_1(X1,X0) <=> v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t101_tops_1)).
% 1.41/0.56  fof(f87,plain,(
% 1.41/0.56    ( ! [X0] : (m1_subset_1(k9_subset_1(u1_struct_0(sK0),X0,sK2),k1_zfmisc_1(u1_struct_0(sK0)))) ) | ~spl3_4),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f58,f32])).
% 1.41/0.56  fof(f32,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f12])).
% 1.41/0.56  fof(f12,plain,(
% 1.41/0.56    ! [X0,X1,X2] : (m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 1.41/0.56    inference(ennf_transformation,[],[f2])).
% 1.41/0.56  fof(f2,axiom,(
% 1.41/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => m1_subset_1(k9_subset_1(X0,X1,X2),k1_zfmisc_1(X0)))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k9_subset_1)).
% 1.41/0.56  fof(f58,plain,(
% 1.41/0.56    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_4),
% 1.41/0.56    inference(avatar_component_clause,[],[f56])).
% 1.41/0.56  fof(f43,plain,(
% 1.41/0.56    ~v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) | spl3_1),
% 1.41/0.56    inference(avatar_component_clause,[],[f41])).
% 1.41/0.56  fof(f68,plain,(
% 1.41/0.56    l1_pre_topc(sK0) | ~spl3_6),
% 1.41/0.56    inference(avatar_component_clause,[],[f66])).
% 1.41/0.56  fof(f446,plain,(
% 1.41/0.56    spl3_60 | ~spl3_52 | ~spl3_57),
% 1.41/0.56    inference(avatar_split_clause,[],[f441,f418,f394,f443])).
% 1.41/0.56  fof(f394,plain,(
% 1.41/0.56    spl3_52 <=> v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)),sK0)),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 1.41/0.56  fof(f418,plain,(
% 1.41/0.56    spl3_57 <=> k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2))),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 1.41/0.56  fof(f441,plain,(
% 1.41/0.56    v5_tops_1(k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)),sK0) | (~spl3_52 | ~spl3_57)),
% 1.41/0.56    inference(backward_demodulation,[],[f396,f420])).
% 1.41/0.56  fof(f420,plain,(
% 1.41/0.56    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) | ~spl3_57),
% 1.41/0.56    inference(avatar_component_clause,[],[f418])).
% 1.41/0.56  fof(f396,plain,(
% 1.41/0.56    v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)),sK0) | ~spl3_52),
% 1.41/0.56    inference(avatar_component_clause,[],[f394])).
% 1.41/0.56  fof(f428,plain,(
% 1.41/0.56    spl3_57 | ~spl3_42 | ~spl3_49),
% 1.41/0.56    inference(avatar_split_clause,[],[f427,f378,f337,f418])).
% 1.41/0.56  fof(f337,plain,(
% 1.41/0.56    spl3_42 <=> k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)))),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 1.41/0.56  fof(f378,plain,(
% 1.41/0.56    spl3_49 <=> k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 1.41/0.56  fof(f427,plain,(
% 1.41/0.56    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k9_subset_1(u1_struct_0(sK0),sK1,sK2)) | (~spl3_42 | ~spl3_49)),
% 1.41/0.56    inference(forward_demodulation,[],[f339,f380])).
% 1.41/0.56  fof(f380,plain,(
% 1.41/0.56    k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)) | ~spl3_49),
% 1.41/0.56    inference(avatar_component_clause,[],[f378])).
% 1.41/0.56  fof(f339,plain,(
% 1.41/0.56    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))) | ~spl3_42),
% 1.41/0.56    inference(avatar_component_clause,[],[f337])).
% 1.41/0.56  fof(f397,plain,(
% 1.41/0.56    spl3_52 | ~spl3_6 | ~spl3_7 | ~spl3_8 | ~spl3_9 | ~spl3_12 | ~spl3_13),
% 1.41/0.56    inference(avatar_split_clause,[],[f282,f111,f106,f83,f78,f71,f66,f394])).
% 1.41/0.56  fof(f71,plain,(
% 1.41/0.56    spl3_7 <=> v2_pre_topc(sK0)),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.41/0.56  fof(f78,plain,(
% 1.41/0.56    spl3_8 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.41/0.56  fof(f83,plain,(
% 1.41/0.56    spl3_9 <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.41/0.56  fof(f106,plain,(
% 1.41/0.56    spl3_12 <=> v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.41/0.56  fof(f111,plain,(
% 1.41/0.56    spl3_13 <=> v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0)),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.41/0.56  fof(f282,plain,(
% 1.41/0.56    v5_tops_1(k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)),sK0) | (~spl3_6 | ~spl3_7 | ~spl3_8 | ~spl3_9 | ~spl3_12 | ~spl3_13)),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f73,f68,f108,f80,f113,f85,f39])).
% 1.41/0.56  fof(f39,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v5_tops_1(X2,X0) | ~v5_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f19])).
% 1.41/0.56  fof(f19,plain,(
% 1.41/0.56    ! [X0] : (! [X1] : (! [X2] : (v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | ~v5_tops_1(X2,X0) | ~v5_tops_1(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.41/0.56    inference(flattening,[],[f18])).
% 1.41/0.56  fof(f18,plain,(
% 1.41/0.56    ! [X0] : (! [X1] : (! [X2] : ((v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) | (~v5_tops_1(X2,X0) | ~v5_tops_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.41/0.56    inference(ennf_transformation,[],[f7])).
% 1.41/0.56  fof(f7,axiom,(
% 1.41/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v5_tops_1(X2,X0) & v5_tops_1(X1,X0)) => v5_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_tops_1)).
% 1.41/0.56  fof(f85,plain,(
% 1.41/0.56    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_9),
% 1.41/0.56    inference(avatar_component_clause,[],[f83])).
% 1.41/0.56  fof(f113,plain,(
% 1.41/0.56    v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0) | ~spl3_13),
% 1.41/0.56    inference(avatar_component_clause,[],[f111])).
% 1.41/0.56  fof(f80,plain,(
% 1.41/0.56    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_8),
% 1.41/0.56    inference(avatar_component_clause,[],[f78])).
% 1.41/0.56  fof(f108,plain,(
% 1.41/0.56    v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~spl3_12),
% 1.41/0.56    inference(avatar_component_clause,[],[f106])).
% 1.41/0.56  fof(f73,plain,(
% 1.41/0.56    v2_pre_topc(sK0) | ~spl3_7),
% 1.41/0.56    inference(avatar_component_clause,[],[f71])).
% 1.41/0.56  fof(f381,plain,(
% 1.41/0.56    spl3_49 | ~spl3_5 | ~spl3_9 | ~spl3_11),
% 1.41/0.56    inference(avatar_split_clause,[],[f376,f98,f83,f61,f378])).
% 1.41/0.56  fof(f61,plain,(
% 1.41/0.56    spl3_5 <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.41/0.56  fof(f98,plain,(
% 1.41/0.56    spl3_11 <=> sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.41/0.56  fof(f376,plain,(
% 1.41/0.56    k9_subset_1(u1_struct_0(sK0),sK1,sK2) = k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)) | (~spl3_5 | ~spl3_9 | ~spl3_11)),
% 1.41/0.56    inference(forward_demodulation,[],[f286,f100])).
% 1.41/0.56  fof(f100,plain,(
% 1.41/0.56    sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) | ~spl3_11),
% 1.41/0.56    inference(avatar_component_clause,[],[f98])).
% 1.41/0.56  fof(f286,plain,(
% 1.41/0.56    k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2)) = k9_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2))) | (~spl3_5 | ~spl3_9)),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f63,f85,f33])).
% 1.41/0.56  fof(f33,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f13])).
% 1.41/0.56  fof(f13,plain,(
% 1.41/0.56    ! [X0,X1] : (! [X2] : (k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.41/0.56    inference(ennf_transformation,[],[f4])).
% 1.41/0.56  fof(f4,axiom,(
% 1.41/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k9_subset_1(X0,X1,k3_subset_1(X0,X2))))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t32_subset_1)).
% 1.41/0.56  fof(f63,plain,(
% 1.41/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 1.41/0.56    inference(avatar_component_clause,[],[f61])).
% 1.41/0.56  fof(f340,plain,(
% 1.41/0.56    spl3_42 | ~spl3_5 | ~spl3_9),
% 1.41/0.56    inference(avatar_split_clause,[],[f294,f83,f61,f337])).
% 1.41/0.56  fof(f294,plain,(
% 1.41/0.56    k4_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK1),k3_subset_1(u1_struct_0(sK0),sK2)) = k3_subset_1(u1_struct_0(sK0),k7_subset_1(u1_struct_0(sK0),sK1,k3_subset_1(u1_struct_0(sK0),sK2))) | (~spl3_5 | ~spl3_9)),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f63,f85,f36])).
% 1.41/0.56  fof(f36,plain,(
% 1.41/0.56    ( ! [X2,X0,X1] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f15])).
% 1.41/0.56  fof(f15,plain,(
% 1.41/0.56    ! [X0,X1] : (! [X2] : (k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.41/0.56    inference(ennf_transformation,[],[f5])).
% 1.41/0.56  fof(f5,axiom,(
% 1.41/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k3_subset_1(X0,k7_subset_1(X0,X1,X2)) = k4_subset_1(X0,k3_subset_1(X0,X1),X2)))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_subset_1)).
% 1.41/0.56  fof(f114,plain,(
% 1.41/0.56    spl3_13 | ~spl3_2 | ~spl3_4 | ~spl3_6),
% 1.41/0.56    inference(avatar_split_clause,[],[f102,f66,f56,f46,f111])).
% 1.41/0.56  fof(f46,plain,(
% 1.41/0.56    spl3_2 <=> v6_tops_1(sK2,sK0)),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.41/0.56  fof(f102,plain,(
% 1.41/0.56    v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0) | (~spl3_2 | ~spl3_4 | ~spl3_6)),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f68,f48,f58,f34])).
% 1.41/0.56  fof(f34,plain,(
% 1.41/0.56    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v6_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v5_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)) )),
% 1.41/0.56    inference(cnf_transformation,[],[f24])).
% 1.41/0.56  fof(f48,plain,(
% 1.41/0.56    v6_tops_1(sK2,sK0) | ~spl3_2),
% 1.41/0.56    inference(avatar_component_clause,[],[f46])).
% 1.41/0.56  fof(f109,plain,(
% 1.41/0.56    spl3_12 | ~spl3_3 | ~spl3_5 | ~spl3_6),
% 1.41/0.56    inference(avatar_split_clause,[],[f103,f66,f61,f51,f106])).
% 1.41/0.56  fof(f51,plain,(
% 1.41/0.56    spl3_3 <=> v6_tops_1(sK1,sK0)),
% 1.41/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.41/0.56  fof(f103,plain,(
% 1.41/0.56    v5_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | (~spl3_3 | ~spl3_5 | ~spl3_6)),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f68,f53,f63,f34])).
% 1.41/0.56  fof(f53,plain,(
% 1.41/0.56    v6_tops_1(sK1,sK0) | ~spl3_3),
% 1.41/0.56    inference(avatar_component_clause,[],[f51])).
% 1.41/0.56  fof(f101,plain,(
% 1.41/0.56    spl3_11 | ~spl3_4),
% 1.41/0.56    inference(avatar_split_clause,[],[f89,f56,f98])).
% 1.41/0.56  fof(f89,plain,(
% 1.41/0.56    sK2 = k3_subset_1(u1_struct_0(sK0),k3_subset_1(u1_struct_0(sK0),sK2)) | ~spl3_4),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f58,f37])).
% 1.41/0.56  fof(f37,plain,(
% 1.41/0.56    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f16])).
% 1.41/0.56  fof(f16,plain,(
% 1.41/0.56    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.41/0.56    inference(ennf_transformation,[],[f3])).
% 1.41/0.56  fof(f3,axiom,(
% 1.41/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 1.41/0.56  fof(f86,plain,(
% 1.41/0.56    spl3_9 | ~spl3_4),
% 1.41/0.56    inference(avatar_split_clause,[],[f75,f56,f83])).
% 1.41/0.56  fof(f75,plain,(
% 1.41/0.56    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_4),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f58,f38])).
% 1.41/0.56  fof(f38,plain,(
% 1.41/0.56    ( ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 1.41/0.56    inference(cnf_transformation,[],[f17])).
% 1.41/0.56  fof(f17,plain,(
% 1.41/0.56    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.41/0.56    inference(ennf_transformation,[],[f1])).
% 1.41/0.56  fof(f1,axiom,(
% 1.41/0.56    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 1.41/0.56  fof(f81,plain,(
% 1.41/0.56    spl3_8 | ~spl3_5),
% 1.41/0.56    inference(avatar_split_clause,[],[f76,f61,f78])).
% 1.41/0.56  fof(f76,plain,(
% 1.41/0.56    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl3_5),
% 1.41/0.56    inference(unit_resulting_resolution,[],[f63,f38])).
% 1.41/0.56  fof(f74,plain,(
% 1.41/0.56    spl3_7),
% 1.41/0.56    inference(avatar_split_clause,[],[f25,f71])).
% 1.41/0.56  fof(f25,plain,(
% 1.41/0.56    v2_pre_topc(sK0)),
% 1.41/0.56    inference(cnf_transformation,[],[f23])).
% 1.41/0.56  fof(f23,plain,(
% 1.41/0.56    ((~v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v6_tops_1(sK2,sK0) & v6_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 1.41/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f11,f22,f21,f20])).
% 1.41/0.56  fof(f20,plain,(
% 1.41/0.56    ? [X0] : (? [X1] : (? [X2] : (~v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v6_tops_1(X2,X0) & v6_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (? [X1] : (? [X2] : (~v6_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v6_tops_1(X2,sK0) & v6_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 1.41/0.56    introduced(choice_axiom,[])).
% 1.41/0.56  fof(f21,plain,(
% 1.41/0.56    ? [X1] : (? [X2] : (~v6_tops_1(k9_subset_1(u1_struct_0(sK0),X1,X2),sK0) & v6_tops_1(X2,sK0) & v6_tops_1(X1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))) => (? [X2] : (~v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v6_tops_1(X2,sK0) & v6_tops_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.41/0.56    introduced(choice_axiom,[])).
% 1.41/0.56  fof(f22,plain,(
% 1.41/0.56    ? [X2] : (~v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,X2),sK0) & v6_tops_1(X2,sK0) & v6_tops_1(sK1,sK0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))) => (~v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) & v6_tops_1(sK2,sK0) & v6_tops_1(sK1,sK0) & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))))),
% 1.41/0.56    introduced(choice_axiom,[])).
% 1.41/0.56  fof(f11,plain,(
% 1.41/0.56    ? [X0] : (? [X1] : (? [X2] : (~v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & v6_tops_1(X2,X0) & v6_tops_1(X1,X0) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.41/0.56    inference(flattening,[],[f10])).
% 1.41/0.56  fof(f10,plain,(
% 1.41/0.56    ? [X0] : (? [X1] : (? [X2] : ((~v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) & (v6_tops_1(X2,X0) & v6_tops_1(X1,X0))) & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.41/0.56    inference(ennf_transformation,[],[f9])).
% 1.41/0.56  fof(f9,negated_conjecture,(
% 1.41/0.56    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v6_tops_1(X2,X0) & v6_tops_1(X1,X0)) => v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 1.41/0.56    inference(negated_conjecture,[],[f8])).
% 1.41/0.56  fof(f8,conjecture,(
% 1.41/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((v6_tops_1(X2,X0) & v6_tops_1(X1,X0)) => v6_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)))))),
% 1.41/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t109_tops_1)).
% 1.41/0.56  fof(f69,plain,(
% 1.41/0.56    spl3_6),
% 1.41/0.56    inference(avatar_split_clause,[],[f26,f66])).
% 1.41/0.56  fof(f26,plain,(
% 1.41/0.56    l1_pre_topc(sK0)),
% 1.41/0.56    inference(cnf_transformation,[],[f23])).
% 1.41/0.56  fof(f64,plain,(
% 1.41/0.56    spl3_5),
% 1.41/0.56    inference(avatar_split_clause,[],[f27,f61])).
% 1.41/0.56  fof(f27,plain,(
% 1.41/0.56    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.41/0.56    inference(cnf_transformation,[],[f23])).
% 1.41/0.56  fof(f59,plain,(
% 1.41/0.56    spl3_4),
% 1.41/0.56    inference(avatar_split_clause,[],[f28,f56])).
% 1.41/0.56  fof(f28,plain,(
% 1.41/0.56    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.41/0.56    inference(cnf_transformation,[],[f23])).
% 1.41/0.56  fof(f54,plain,(
% 1.41/0.56    spl3_3),
% 1.41/0.56    inference(avatar_split_clause,[],[f29,f51])).
% 1.41/0.56  fof(f29,plain,(
% 1.41/0.56    v6_tops_1(sK1,sK0)),
% 1.41/0.56    inference(cnf_transformation,[],[f23])).
% 1.41/0.56  fof(f49,plain,(
% 1.41/0.56    spl3_2),
% 1.41/0.56    inference(avatar_split_clause,[],[f30,f46])).
% 1.41/0.56  fof(f30,plain,(
% 1.41/0.56    v6_tops_1(sK2,sK0)),
% 1.41/0.56    inference(cnf_transformation,[],[f23])).
% 1.41/0.56  fof(f44,plain,(
% 1.41/0.56    ~spl3_1),
% 1.41/0.56    inference(avatar_split_clause,[],[f31,f41])).
% 1.41/0.56  fof(f31,plain,(
% 1.41/0.56    ~v6_tops_1(k9_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)),
% 1.41/0.56    inference(cnf_transformation,[],[f23])).
% 1.41/0.56  % SZS output end Proof for theBenchmark
% 1.41/0.56  % (1853)------------------------------
% 1.41/0.56  % (1853)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.41/0.56  % (1853)Termination reason: Refutation
% 1.41/0.56  
% 1.41/0.56  % (1853)Memory used [KB]: 11129
% 1.41/0.56  % (1853)Time elapsed: 0.101 s
% 1.41/0.56  % (1853)------------------------------
% 1.41/0.56  % (1853)------------------------------
% 1.41/0.56  % (1846)Success in time 0.195 s
%------------------------------------------------------------------------------
