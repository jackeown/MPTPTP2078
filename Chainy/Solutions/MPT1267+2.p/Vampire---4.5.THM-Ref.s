%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1267+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:15 EST 2020

% Result     : Theorem 24.90s
% Output     : Refutation 24.90s
% Verified   : 
% Statistics : Number of formulae       :  143 ( 319 expanded)
%              Number of leaves         :   35 ( 135 expanded)
%              Depth                    :   13
%              Number of atoms          :  462 (1266 expanded)
%              Number of equality atoms :   28 (  58 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f39955,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f3507,f3512,f3517,f3522,f3527,f3537,f3547,f3562,f3652,f4417,f4614,f4628,f4634,f7715,f7720,f7730,f26727,f26732,f39381])).

fof(f39381,plain,
    ( ~ spl99_1
    | ~ spl99_2
    | spl99_20
    | ~ spl99_35
    | ~ spl99_87
    | ~ spl99_88
    | ~ spl99_90
    | ~ spl99_171
    | ~ spl99_172 ),
    inference(avatar_contradiction_clause,[],[f39380])).

fof(f39380,plain,
    ( $false
    | ~ spl99_1
    | ~ spl99_2
    | spl99_20
    | ~ spl99_35
    | ~ spl99_87
    | ~ spl99_88
    | ~ spl99_90
    | ~ spl99_171
    | ~ spl99_172 ),
    inference(subsumption_resolution,[],[f39379,f7619])).

fof(f7619,plain,
    ( ~ v1_tops_1(k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK1)),sK0)
    | ~ spl99_2
    | spl99_20
    | ~ spl99_35 ),
    inference(backward_demodulation,[],[f4436,f7343])).

fof(f7343,plain,
    ( k3_subset_1(u1_struct_0(sK0),k2_xboole_0(sK2,sK1)) = k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK1))
    | ~ spl99_35 ),
    inference(unit_resulting_resolution,[],[f4416,f2977])).

fof(f2977,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    inference(cnf_transformation,[],[f2305])).

fof(f2305,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f462])).

fof(f462,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_subset_1)).

fof(f4416,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl99_35 ),
    inference(avatar_component_clause,[],[f4414])).

fof(f4414,plain,
    ( spl99_35
  <=> m1_subset_1(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_35])])).

fof(f4436,plain,
    ( ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),k2_xboole_0(sK2,sK1)),sK0)
    | ~ spl99_2
    | spl99_20
    | ~ spl99_35 ),
    inference(unit_resulting_resolution,[],[f3511,f3651,f4416,f2860])).

fof(f2860,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2608])).

fof(f2608,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v2_tops_1(X1,X0)
              | ~ v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v2_tops_1(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2228])).

fof(f2228,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2091])).

fof(f2091,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tops_1(X1,X0)
          <=> v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_1)).

fof(f3651,plain,
    ( ~ v2_tops_1(k2_xboole_0(sK2,sK1),sK0)
    | spl99_20 ),
    inference(avatar_component_clause,[],[f3649])).

fof(f3649,plain,
    ( spl99_20
  <=> v2_tops_1(k2_xboole_0(sK2,sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_20])])).

fof(f3511,plain,
    ( l1_pre_topc(sK0)
    | ~ spl99_2 ),
    inference(avatar_component_clause,[],[f3509])).

fof(f3509,plain,
    ( spl99_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_2])])).

fof(f39379,plain,
    ( v1_tops_1(k4_xboole_0(u1_struct_0(sK0),k2_xboole_0(sK2,sK1)),sK0)
    | ~ spl99_1
    | ~ spl99_2
    | ~ spl99_87
    | ~ spl99_88
    | ~ spl99_90
    | ~ spl99_171
    | ~ spl99_172 ),
    inference(forward_demodulation,[],[f39378,f3079])).

fof(f3079,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(cnf_transformation,[],[f2169])).

fof(f2169,plain,(
    ! [X0] : k3_xboole_0(X0,X0) = X0 ),
    inference(rectify,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

fof(f39378,plain,
    ( v1_tops_1(k4_xboole_0(k3_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),k2_xboole_0(sK2,sK1)),sK0)
    | ~ spl99_1
    | ~ spl99_2
    | ~ spl99_87
    | ~ spl99_88
    | ~ spl99_90
    | ~ spl99_171
    | ~ spl99_172 ),
    inference(forward_demodulation,[],[f39377,f2909])).

fof(f2909,plain,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_xboole_0(X0,X1) = k2_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

fof(f39377,plain,
    ( v1_tops_1(k4_xboole_0(k3_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),k2_xboole_0(sK1,sK2)),sK0)
    | ~ spl99_1
    | ~ spl99_2
    | ~ spl99_87
    | ~ spl99_88
    | ~ spl99_90
    | ~ spl99_171
    | ~ spl99_172 ),
    inference(forward_demodulation,[],[f39376,f3334])).

fof(f3334,plain,(
    ! [X2,X0,X1] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f103])).

fof(f103,axiom,(
    ! [X0,X1,X2] : k4_xboole_0(X0,k2_xboole_0(X1,X2)) = k4_xboole_0(k4_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_xboole_1)).

fof(f39376,plain,
    ( v1_tops_1(k4_xboole_0(k4_xboole_0(k3_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)),sK1),sK2),sK0)
    | ~ spl99_1
    | ~ spl99_2
    | ~ spl99_87
    | ~ spl99_88
    | ~ spl99_90
    | ~ spl99_171
    | ~ spl99_172 ),
    inference(forward_demodulation,[],[f39375,f3333])).

fof(f3333,plain,(
    ! [X2,X0,X1] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    inference(cnf_transformation,[],[f111])).

fof(f111,axiom,(
    ! [X0,X1,X2] : k3_xboole_0(X0,k4_xboole_0(X1,X2)) = k4_xboole_0(k3_xboole_0(X0,X1),X2) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_xboole_1)).

fof(f39375,plain,
    ( v1_tops_1(k4_xboole_0(k3_xboole_0(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1)),sK2),sK0)
    | ~ spl99_1
    | ~ spl99_2
    | ~ spl99_87
    | ~ spl99_88
    | ~ spl99_90
    | ~ spl99_171
    | ~ spl99_172 ),
    inference(forward_demodulation,[],[f39374,f3077])).

fof(f3077,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k3_xboole_0(X1,X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

fof(f39374,plain,
    ( v1_tops_1(k4_xboole_0(k3_xboole_0(k4_xboole_0(u1_struct_0(sK0),sK1),u1_struct_0(sK0)),sK2),sK0)
    | ~ spl99_1
    | ~ spl99_2
    | ~ spl99_87
    | ~ spl99_88
    | ~ spl99_90
    | ~ spl99_171
    | ~ spl99_172 ),
    inference(forward_demodulation,[],[f38068,f35913])).

fof(f35913,plain,
    ( ! [X0] : k4_xboole_0(k3_xboole_0(X0,u1_struct_0(sK0)),sK2) = k9_subset_1(u1_struct_0(sK0),X0,k4_xboole_0(u1_struct_0(sK0),sK2))
    | ~ spl99_171 ),
    inference(forward_demodulation,[],[f35690,f3333])).

fof(f35690,plain,
    ( ! [X0] : k3_xboole_0(X0,k4_xboole_0(u1_struct_0(sK0),sK2)) = k9_subset_1(u1_struct_0(sK0),X0,k4_xboole_0(u1_struct_0(sK0),sK2))
    | ~ spl99_171 ),
    inference(unit_resulting_resolution,[],[f26726,f3083])).

fof(f3083,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2382])).

fof(f2382,plain,(
    ! [X0,X1,X2] :
      ( k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f496])).

fof(f496,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k3_xboole_0(X1,X2) = k9_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f26726,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl99_171 ),
    inference(avatar_component_clause,[],[f26724])).

fof(f26724,plain,
    ( spl99_171
  <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_171])])).

fof(f38068,plain,
    ( v1_tops_1(k9_subset_1(u1_struct_0(sK0),k4_xboole_0(u1_struct_0(sK0),sK1),k4_xboole_0(u1_struct_0(sK0),sK2)),sK0)
    | ~ spl99_1
    | ~ spl99_2
    | ~ spl99_87
    | ~ spl99_88
    | ~ spl99_90
    | ~ spl99_171
    | ~ spl99_172 ),
    inference(unit_resulting_resolution,[],[f3506,f3511,f7714,f7719,f26726,f7729,f26731,f3127])).

fof(f3127,plain,(
    ! [X2,X0,X1] :
      ( v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
      | ~ v3_pre_topc(X2,X0)
      | ~ v1_tops_1(X2,X0)
      | ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2415])).

fof(f2415,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v3_pre_topc(X2,X0)
              | ~ v1_tops_1(X2,X0)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2414])).

fof(f2414,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0)
              | ~ v3_pre_topc(X2,X0)
              | ~ v1_tops_1(X2,X0)
              | ~ v1_tops_1(X1,X0)
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2164])).

fof(f2164,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v3_pre_topc(X2,X0)
                  & v1_tops_1(X2,X0)
                  & v1_tops_1(X1,X0) )
               => v1_tops_1(k9_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_tops_1)).

fof(f26731,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl99_172 ),
    inference(avatar_component_clause,[],[f26729])).

fof(f26729,plain,
    ( spl99_172
  <=> m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_172])])).

fof(f7729,plain,
    ( v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl99_90 ),
    inference(avatar_component_clause,[],[f7727])).

fof(f7727,plain,
    ( spl99_90
  <=> v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_90])])).

fof(f7719,plain,
    ( v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK2),sK0)
    | ~ spl99_88 ),
    inference(avatar_component_clause,[],[f7717])).

fof(f7717,plain,
    ( spl99_88
  <=> v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_88])])).

fof(f7714,plain,
    ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0)
    | ~ spl99_87 ),
    inference(avatar_component_clause,[],[f7712])).

fof(f7712,plain,
    ( spl99_87
  <=> v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_87])])).

fof(f3506,plain,
    ( v2_pre_topc(sK0)
    | ~ spl99_1 ),
    inference(avatar_component_clause,[],[f3504])).

fof(f3504,plain,
    ( spl99_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_1])])).

fof(f26732,plain,
    ( spl99_172
    | ~ spl99_7 ),
    inference(avatar_split_clause,[],[f7515,f3534,f26729])).

fof(f3534,plain,
    ( spl99_7
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_7])])).

fof(f7515,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl99_7 ),
    inference(backward_demodulation,[],[f6870,f7346])).

fof(f7346,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl99_7 ),
    inference(unit_resulting_resolution,[],[f3536,f2977])).

fof(f3536,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl99_7 ),
    inference(avatar_component_clause,[],[f3534])).

fof(f6870,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl99_7 ),
    inference(unit_resulting_resolution,[],[f3536,f2978])).

fof(f2978,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2306])).

fof(f2306,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f466])).

fof(f466,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f26727,plain,
    ( spl99_171
    | ~ spl99_9 ),
    inference(avatar_split_clause,[],[f7475,f3544,f26724])).

fof(f3544,plain,
    ( spl99_9
  <=> m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_9])])).

fof(f7475,plain,
    ( m1_subset_1(k4_xboole_0(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl99_9 ),
    inference(backward_demodulation,[],[f6871,f7347])).

fof(f7347,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK2) = k4_xboole_0(u1_struct_0(sK0),sK2)
    | ~ spl99_9 ),
    inference(unit_resulting_resolution,[],[f3546,f2977])).

fof(f3546,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl99_9 ),
    inference(avatar_component_clause,[],[f3544])).

fof(f6871,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl99_9 ),
    inference(unit_resulting_resolution,[],[f3546,f2978])).

fof(f7730,plain,
    ( spl99_90
    | ~ spl99_7
    | ~ spl99_37 ),
    inference(avatar_split_clause,[],[f7489,f4625,f3534,f7727])).

fof(f4625,plain,
    ( spl99_37
  <=> v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_37])])).

fof(f7489,plain,
    ( v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK1),sK0)
    | ~ spl99_7
    | ~ spl99_37 ),
    inference(backward_demodulation,[],[f4627,f7346])).

fof(f4627,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl99_37 ),
    inference(avatar_component_clause,[],[f4625])).

fof(f7720,plain,
    ( spl99_88
    | ~ spl99_9
    | ~ spl99_38 ),
    inference(avatar_split_clause,[],[f7448,f4631,f3544,f7717])).

fof(f4631,plain,
    ( spl99_38
  <=> v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_38])])).

fof(f7448,plain,
    ( v1_tops_1(k4_xboole_0(u1_struct_0(sK0),sK2),sK0)
    | ~ spl99_9
    | ~ spl99_38 ),
    inference(backward_demodulation,[],[f4633,f7347])).

fof(f4633,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
    | ~ spl99_38 ),
    inference(avatar_component_clause,[],[f4631])).

fof(f7715,plain,
    ( spl99_87
    | ~ spl99_9
    | ~ spl99_36 ),
    inference(avatar_split_clause,[],[f7447,f4611,f3544,f7712])).

fof(f4611,plain,
    ( spl99_36
  <=> v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_36])])).

fof(f7447,plain,
    ( v3_pre_topc(k4_xboole_0(u1_struct_0(sK0),sK2),sK0)
    | ~ spl99_9
    | ~ spl99_36 ),
    inference(backward_demodulation,[],[f4613,f7347])).

fof(f4613,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
    | ~ spl99_36 ),
    inference(avatar_component_clause,[],[f4611])).

fof(f4634,plain,
    ( spl99_38
    | ~ spl99_2
    | ~ spl99_4
    | ~ spl99_9 ),
    inference(avatar_split_clause,[],[f3660,f3544,f3519,f3509,f4631])).

fof(f3519,plain,
    ( spl99_4
  <=> v2_tops_1(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_4])])).

fof(f3660,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
    | ~ spl99_2
    | ~ spl99_4
    | ~ spl99_9 ),
    inference(unit_resulting_resolution,[],[f3511,f3521,f3546,f2859])).

fof(f2859,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v2_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2608])).

fof(f3521,plain,
    ( v2_tops_1(sK2,sK0)
    | ~ spl99_4 ),
    inference(avatar_component_clause,[],[f3519])).

fof(f4628,plain,
    ( spl99_37
    | ~ spl99_2
    | ~ spl99_3
    | ~ spl99_7 ),
    inference(avatar_split_clause,[],[f3659,f3534,f3514,f3509,f4625])).

fof(f3514,plain,
    ( spl99_3
  <=> v2_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_3])])).

fof(f3659,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl99_2
    | ~ spl99_3
    | ~ spl99_7 ),
    inference(unit_resulting_resolution,[],[f3511,f3516,f3536,f2859])).

fof(f3516,plain,
    ( v2_tops_1(sK1,sK0)
    | ~ spl99_3 ),
    inference(avatar_component_clause,[],[f3514])).

fof(f4614,plain,
    ( spl99_36
    | ~ spl99_2
    | ~ spl99_5
    | ~ spl99_9 ),
    inference(avatar_split_clause,[],[f3653,f3544,f3524,f3509,f4611])).

fof(f3524,plain,
    ( spl99_5
  <=> v4_pre_topc(sK2,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_5])])).

fof(f3653,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK2),sK0)
    | ~ spl99_2
    | ~ spl99_5
    | ~ spl99_9 ),
    inference(unit_resulting_resolution,[],[f3511,f3526,f3546,f2851])).

fof(f2851,plain,(
    ! [X0,X1] :
      ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f2604])).

fof(f2604,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
            & ( v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(nnf_transformation,[],[f2223])).

fof(f2223,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2120])).

fof(f2120,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_tops_1)).

fof(f3526,plain,
    ( v4_pre_topc(sK2,sK0)
    | ~ spl99_5 ),
    inference(avatar_component_clause,[],[f3524])).

fof(f4417,plain,
    ( spl99_35
    | ~ spl99_7
    | ~ spl99_9 ),
    inference(avatar_split_clause,[],[f3641,f3544,f3534,f4414])).

fof(f3641,plain,
    ( m1_subset_1(k2_xboole_0(sK2,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl99_7
    | ~ spl99_9 ),
    inference(backward_demodulation,[],[f3608,f3640])).

fof(f3640,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK2,sK1)
    | ~ spl99_7
    | ~ spl99_9 ),
    inference(forward_demodulation,[],[f3626,f2909])).

fof(f3626,plain,
    ( k4_subset_1(u1_struct_0(sK0),sK1,sK2) = k2_xboole_0(sK1,sK2)
    | ~ spl99_7
    | ~ spl99_9 ),
    inference(unit_resulting_resolution,[],[f3536,f3546,f2807])).

fof(f2807,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2178])).

fof(f2178,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f2177])).

fof(f2177,plain,(
    ! [X0,X1,X2] :
      ( k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f491])).

fof(f491,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => k2_xboole_0(X1,X2) = k4_subset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k4_subset_1)).

fof(f3608,plain,
    ( m1_subset_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl99_7
    | ~ spl99_9 ),
    inference(unit_resulting_resolution,[],[f3536,f3546,f2808])).

fof(f2808,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f2180])).

fof(f2180,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f2179])).

fof(f2179,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f467])).

fof(f467,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
        & m1_subset_1(X1,k1_zfmisc_1(X0)) )
     => m1_subset_1(k4_subset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_subset_1)).

fof(f3652,plain,
    ( ~ spl99_20
    | ~ spl99_7
    | ~ spl99_9
    | spl99_12 ),
    inference(avatar_split_clause,[],[f3642,f3559,f3544,f3534,f3649])).

fof(f3559,plain,
    ( spl99_12
  <=> v2_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl99_12])])).

fof(f3642,plain,
    ( ~ v2_tops_1(k2_xboole_0(sK2,sK1),sK0)
    | ~ spl99_7
    | ~ spl99_9
    | spl99_12 ),
    inference(backward_demodulation,[],[f3561,f3640])).

fof(f3561,plain,
    ( ~ v2_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    | spl99_12 ),
    inference(avatar_component_clause,[],[f3559])).

fof(f3562,plain,(
    ~ spl99_12 ),
    inference(avatar_split_clause,[],[f2805,f3559])).

fof(f2805,plain,(
    ~ v2_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0) ),
    inference(cnf_transformation,[],[f2582])).

fof(f2582,plain,
    ( ~ v2_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
    & v4_pre_topc(sK2,sK0)
    & v2_tops_1(sK2,sK0)
    & v2_tops_1(sK1,sK0)
    & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0)))
    & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f2174,f2581,f2580,f2579])).

fof(f2579,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
                & v4_pre_topc(X2,X0)
                & v2_tops_1(X2,X0)
                & v2_tops_1(X1,X0)
                & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_1(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0)
              & v4_pre_topc(X2,sK0)
              & v2_tops_1(X2,sK0)
              & v2_tops_1(X1,sK0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f2580,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ v2_tops_1(k4_subset_1(u1_struct_0(sK0),X1,X2),sK0)
            & v4_pre_topc(X2,sK0)
            & v2_tops_1(X2,sK0)
            & v2_tops_1(X1,sK0)
            & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
        & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ? [X2] :
          ( ~ v2_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
          & v4_pre_topc(X2,sK0)
          & v2_tops_1(X2,sK0)
          & v2_tops_1(sK1,sK0)
          & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
      & m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2581,plain,
    ( ? [X2] :
        ( ~ v2_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,X2),sK0)
        & v4_pre_topc(X2,sK0)
        & v2_tops_1(X2,sK0)
        & v2_tops_1(sK1,sK0)
        & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) )
   => ( ~ v2_tops_1(k4_subset_1(u1_struct_0(sK0),sK1,sK2),sK0)
      & v4_pre_topc(sK2,sK0)
      & v2_tops_1(sK2,sK0)
      & v2_tops_1(sK1,sK0)
      & m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(choice_axiom,[])).

fof(f2174,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v4_pre_topc(X2,X0)
              & v2_tops_1(X2,X0)
              & v2_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f2173])).

fof(f2173,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0)
              & v4_pre_topc(X2,X0)
              & v2_tops_1(X2,X0)
              & v2_tops_1(X1,X0)
              & m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2167])).

fof(f2167,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( ( v4_pre_topc(X2,X0)
                    & v2_tops_1(X2,X0)
                    & v2_tops_1(X1,X0) )
                 => v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f2166])).

fof(f2166,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( ( v4_pre_topc(X2,X0)
                  & v2_tops_1(X2,X0)
                  & v2_tops_1(X1,X0) )
               => v2_tops_1(k4_subset_1(u1_struct_0(X0),X1,X2),X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_tops_1)).

fof(f3547,plain,(
    spl99_9 ),
    inference(avatar_split_clause,[],[f2801,f3544])).

fof(f2801,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2582])).

fof(f3537,plain,(
    spl99_7 ),
    inference(avatar_split_clause,[],[f2800,f3534])).

fof(f2800,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f2582])).

fof(f3527,plain,(
    spl99_5 ),
    inference(avatar_split_clause,[],[f2804,f3524])).

fof(f2804,plain,(
    v4_pre_topc(sK2,sK0) ),
    inference(cnf_transformation,[],[f2582])).

fof(f3522,plain,(
    spl99_4 ),
    inference(avatar_split_clause,[],[f2803,f3519])).

fof(f2803,plain,(
    v2_tops_1(sK2,sK0) ),
    inference(cnf_transformation,[],[f2582])).

fof(f3517,plain,(
    spl99_3 ),
    inference(avatar_split_clause,[],[f2802,f3514])).

fof(f2802,plain,(
    v2_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f2582])).

fof(f3512,plain,(
    spl99_2 ),
    inference(avatar_split_clause,[],[f2799,f3509])).

fof(f2799,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2582])).

fof(f3507,plain,(
    spl99_1 ),
    inference(avatar_split_clause,[],[f2798,f3504])).

fof(f2798,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f2582])).
%------------------------------------------------------------------------------
