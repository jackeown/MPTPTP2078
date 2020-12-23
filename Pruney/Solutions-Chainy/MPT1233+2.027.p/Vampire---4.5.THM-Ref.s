%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:11:00 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  109 ( 178 expanded)
%              Number of leaves         :   29 (  79 expanded)
%              Depth                    :    9
%              Number of atoms          :  292 ( 448 expanded)
%              Number of equality atoms :   71 ( 109 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f221,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f73,f78,f86,f89,f96,f104,f111,f116,f160,f203,f212,f220])).

fof(f220,plain,
    ( ~ spl1_3
    | ~ spl1_2
    | ~ spl1_24
    | ~ spl1_4
    | spl1_25 ),
    inference(avatar_split_clause,[],[f214,f200,f64,f197,f56,f60])).

fof(f60,plain,
    ( spl1_3
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f56,plain,
    ( spl1_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f197,plain,
    ( spl1_24
  <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_24])])).

fof(f64,plain,
    ( spl1_4
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f200,plain,
    ( spl1_25
  <=> v4_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_25])])).

fof(f214,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | spl1_25 ),
    inference(resolution,[],[f201,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
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
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f201,plain,
    ( ~ v4_pre_topc(k1_xboole_0,sK0)
    | spl1_25 ),
    inference(avatar_component_clause,[],[f200])).

fof(f212,plain,(
    spl1_24 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | spl1_24 ),
    inference(resolution,[],[f198,f37])).

fof(f37,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f198,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | spl1_24 ),
    inference(avatar_component_clause,[],[f197])).

fof(f203,plain,
    ( ~ spl1_2
    | ~ spl1_24
    | ~ spl1_25
    | spl1_6
    | ~ spl1_12
    | ~ spl1_17 ),
    inference(avatar_split_clause,[],[f195,f156,f114,f76,f200,f197,f56])).

fof(f76,plain,
    ( spl1_6
  <=> u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f114,plain,
    ( spl1_12
  <=> u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f156,plain,
    ( spl1_17
  <=> k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f195,plain,
    ( u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))
    | ~ v4_pre_topc(k1_xboole_0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl1_12
    | ~ spl1_17 ),
    inference(forward_demodulation,[],[f193,f115])).

fof(f115,plain,
    ( u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f114])).

fof(f193,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ v4_pre_topc(k1_xboole_0,sK0)
    | ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | ~ spl1_17 ),
    inference(superposition,[],[f157,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f157,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0))
    | ~ spl1_17 ),
    inference(avatar_component_clause,[],[f156])).

fof(f160,plain,
    ( spl1_17
    | ~ spl1_2
    | ~ spl1_8
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f159,f108,f84,f56,f156])).

fof(f84,plain,
    ( spl1_8
  <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f108,plain,
    ( spl1_11
  <=> k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f159,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0))
    | ~ spl1_2
    | ~ spl1_8
    | ~ spl1_11 ),
    inference(forward_demodulation,[],[f147,f109])).

fof(f109,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f147,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl1_2
    | ~ spl1_8 ),
    inference(resolution,[],[f144,f85])).

fof(f85,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f84])).

fof(f144,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) )
    | ~ spl1_2 ),
    inference(resolution,[],[f43,f57])).

fof(f57,plain,
    ( l1_pre_topc(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f56])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f116,plain,
    ( ~ spl1_8
    | spl1_12
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f112,f108,f114,f84])).

fof(f112,plain,
    ( u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl1_11 ),
    inference(superposition,[],[f48,f109])).

fof(f48,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,k3_subset_1(X0,X1)) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).

fof(f111,plain,
    ( ~ spl1_8
    | spl1_11
    | ~ spl1_10 ),
    inference(avatar_split_clause,[],[f106,f101,f108,f84])).

fof(f101,plain,
    ( spl1_10
  <=> k1_xboole_0 = k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f106,plain,
    ( k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl1_10 ),
    inference(superposition,[],[f47,f102])).

fof(f102,plain,
    ( k1_xboole_0 = k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl1_10 ),
    inference(avatar_component_clause,[],[f101])).

fof(f47,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f104,plain,
    ( ~ spl1_8
    | spl1_10
    | ~ spl1_9 ),
    inference(avatar_split_clause,[],[f98,f94,f101,f84])).

fof(f94,plain,
    ( spl1_9
  <=> k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f98,plain,
    ( k1_xboole_0 = k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl1_9 ),
    inference(superposition,[],[f95,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).

fof(f95,plain,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f94])).

fof(f96,plain,
    ( spl1_9
    | ~ spl1_2
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f92,f71,f56,f94])).

fof(f71,plain,
    ( spl1_5
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f92,plain,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))
    | ~ spl1_2
    | ~ spl1_5 ),
    inference(forward_demodulation,[],[f91,f72])).

fof(f72,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f71])).

fof(f91,plain,
    ( k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ spl1_2 ),
    inference(resolution,[],[f90,f57])).

fof(f90,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k2_struct_0(X0)) ) ),
    inference(resolution,[],[f67,f42])).

fof(f42,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f67,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k2_struct_0(X0)) ) ),
    inference(global_subsumption,[],[f39,f50])).

fof(f50,plain,(
    ! [X0] :
      ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k2_struct_0(X0))
      | ~ m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(equality_resolution,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k2_struct_0(X0) != X1
      | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( k2_struct_0(X0) != X1
              | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            & ( k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
              | k2_struct_0(X0) = X1 ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ~ ( k2_struct_0(X0) = X1
                & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) )
            & ~ ( k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)
                & k2_struct_0(X0) != X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_pre_topc)).

fof(f39,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).

fof(f89,plain,
    ( ~ spl1_2
    | spl1_7 ),
    inference(avatar_split_clause,[],[f87,f81,f56])).

fof(f81,plain,
    ( spl1_7
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).

fof(f87,plain,
    ( ~ l1_pre_topc(sK0)
    | spl1_7 ),
    inference(resolution,[],[f82,f42])).

fof(f82,plain,
    ( ~ l1_struct_0(sK0)
    | spl1_7 ),
    inference(avatar_component_clause,[],[f81])).

fof(f86,plain,
    ( ~ spl1_7
    | spl1_8
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f79,f71,f84,f81])).

fof(f79,plain,
    ( m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_struct_0(sK0)
    | ~ spl1_5 ),
    inference(superposition,[],[f39,f72])).

fof(f78,plain,
    ( ~ spl1_6
    | spl1_1
    | ~ spl1_5 ),
    inference(avatar_split_clause,[],[f74,f71,f52,f76])).

fof(f52,plain,
    ( spl1_1
  <=> k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f74,plain,
    ( u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0))
    | spl1_1
    | ~ spl1_5 ),
    inference(superposition,[],[f53,f72])).

fof(f53,plain,
    ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
    | spl1_1 ),
    inference(avatar_component_clause,[],[f52])).

fof(f73,plain,
    ( spl1_5
    | ~ spl1_2 ),
    inference(avatar_split_clause,[],[f69,f56,f71])).

fof(f69,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl1_2 ),
    inference(resolution,[],[f68,f57])).

fof(f68,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(resolution,[],[f38,f42])).

fof(f38,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f66,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f36,f64])).

fof(f36,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f62,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f33,f60])).

fof(f33,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,
    ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f31])).

fof(f31,plain,
    ( ? [X0] :
        ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f18,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

fof(f58,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f34,f56])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f32])).

fof(f54,plain,(
    ~ spl1_1 ),
    inference(avatar_split_clause,[],[f35,f52])).

fof(f35,plain,(
    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f32])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 17:45:29 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.46  % (18805)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.47  % (18804)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.47  % (18813)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.48  % (18805)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f221,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f54,f58,f62,f66,f73,f78,f86,f89,f96,f104,f111,f116,f160,f203,f212,f220])).
% 0.21/0.48  fof(f220,plain,(
% 0.21/0.48    ~spl1_3 | ~spl1_2 | ~spl1_24 | ~spl1_4 | spl1_25),
% 0.21/0.48    inference(avatar_split_clause,[],[f214,f200,f64,f197,f56,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    spl1_3 <=> v2_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    spl1_2 <=> l1_pre_topc(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.21/0.48  fof(f197,plain,(
% 0.21/0.48    spl1_24 <=> m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_24])])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    spl1_4 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.21/0.48  fof(f200,plain,(
% 0.21/0.48    spl1_25 <=> v4_pre_topc(k1_xboole_0,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_25])])).
% 0.21/0.48  fof(f214,plain,(
% 0.21/0.48    ~v1_xboole_0(k1_xboole_0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | spl1_25),
% 0.21/0.48    inference(resolution,[],[f201,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    ~v4_pre_topc(k1_xboole_0,sK0) | spl1_25),
% 0.21/0.48    inference(avatar_component_clause,[],[f200])).
% 0.21/0.48  fof(f212,plain,(
% 0.21/0.48    spl1_24),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f211])).
% 0.21/0.48  fof(f211,plain,(
% 0.21/0.48    $false | spl1_24),
% 0.21/0.48    inference(resolution,[],[f198,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | spl1_24),
% 0.21/0.48    inference(avatar_component_clause,[],[f197])).
% 0.21/0.48  fof(f203,plain,(
% 0.21/0.48    ~spl1_2 | ~spl1_24 | ~spl1_25 | spl1_6 | ~spl1_12 | ~spl1_17),
% 0.21/0.48    inference(avatar_split_clause,[],[f195,f156,f114,f76,f200,f197,f56])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    spl1_6 <=> u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    spl1_12 <=> u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.21/0.48  fof(f156,plain,(
% 0.21/0.48    spl1_17 <=> k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 0.21/0.48  fof(f195,plain,(
% 0.21/0.48    u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) | ~v4_pre_topc(k1_xboole_0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | (~spl1_12 | ~spl1_17)),
% 0.21/0.48    inference(forward_demodulation,[],[f193,f115])).
% 0.21/0.48  fof(f115,plain,(
% 0.21/0.48    u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | ~spl1_12),
% 0.21/0.48    inference(avatar_component_clause,[],[f114])).
% 0.21/0.48  fof(f193,plain,(
% 0.21/0.48    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | ~v4_pre_topc(k1_xboole_0,sK0) | ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~spl1_17),
% 0.21/0.48    inference(superposition,[],[f157,f44])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.48  fof(f157,plain,(
% 0.21/0.48    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0)) | ~spl1_17),
% 0.21/0.48    inference(avatar_component_clause,[],[f156])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    spl1_17 | ~spl1_2 | ~spl1_8 | ~spl1_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f159,f108,f84,f56,f156])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    spl1_8 <=> m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    spl1_11 <=> k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.21/0.48  fof(f159,plain,(
% 0.21/0.48    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0)) | (~spl1_2 | ~spl1_8 | ~spl1_11)),
% 0.21/0.48    inference(forward_demodulation,[],[f147,f109])).
% 0.21/0.48  fof(f109,plain,(
% 0.21/0.48    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl1_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f108])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | (~spl1_2 | ~spl1_8)),
% 0.21/0.48    inference(resolution,[],[f144,f85])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl1_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f84])).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) ) | ~spl1_2),
% 0.21/0.48    inference(resolution,[],[f43,f57])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    l1_pre_topc(sK0) | ~spl1_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f56])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    ~spl1_8 | spl1_12 | ~spl1_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f112,f108,f114,f84])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    u1_struct_0(sK0) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl1_11),
% 0.21/0.48    inference(superposition,[],[f48,f109])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1] : (k3_subset_1(X0,k3_subset_1(X0,X1)) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,k3_subset_1(X0,X1)) = X1)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',involutiveness_k3_subset_1)).
% 0.21/0.48  fof(f111,plain,(
% 0.21/0.48    ~spl1_8 | spl1_11 | ~spl1_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f106,f101,f108,f84])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    spl1_10 <=> k1_xboole_0 = k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    k1_xboole_0 = k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl1_10),
% 0.21/0.48    inference(superposition,[],[f47,f102])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl1_10),
% 0.21/0.48    inference(avatar_component_clause,[],[f101])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0,X1] : (k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    ~spl1_8 | spl1_10 | ~spl1_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f98,f94,f101,f84])).
% 0.21/0.48  fof(f94,plain,(
% 0.21/0.48    spl1_9 <=> k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.21/0.48  fof(f98,plain,(
% 0.21/0.48    k1_xboole_0 = k4_xboole_0(u1_struct_0(sK0),u1_struct_0(sK0)) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl1_9),
% 0.21/0.48    inference(superposition,[],[f95,f49])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k7_subset_1(X0,X1,X2) = k4_xboole_0(X1,X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k7_subset_1)).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0)) | ~spl1_9),
% 0.21/0.48    inference(avatar_component_clause,[],[f94])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    spl1_9 | ~spl1_2 | ~spl1_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f92,f71,f56,f94])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    spl1_5 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK0)) | (~spl1_2 | ~spl1_5)),
% 0.21/0.48    inference(forward_demodulation,[],[f91,f72])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl1_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f71])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    k1_xboole_0 = k7_subset_1(u1_struct_0(sK0),k2_struct_0(sK0),k2_struct_0(sK0)) | ~spl1_2),
% 0.21/0.48    inference(resolution,[],[f90,f57])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_pre_topc(X0) | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k2_struct_0(X0))) )),
% 0.21/0.48    inference(resolution,[],[f67,f42])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_struct_0(X0) | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k2_struct_0(X0))) )),
% 0.21/0.48    inference(global_subsumption,[],[f39,f50])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),k2_struct_0(X0)) | ~m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    ( ! [X0,X1] : (k2_struct_0(X0) != X1 | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (((k2_struct_0(X0) != X1 | k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & (k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) | k2_struct_0(X0) = X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_struct_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (~(k2_struct_0(X0) = X1 & k1_xboole_0 != k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1)) & ~(k1_xboole_0 = k7_subset_1(u1_struct_0(X0),k2_struct_0(X0),X1) & k2_struct_0(X0) != X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_pre_topc)).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0] : (m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) => m1_subset_1(k2_struct_0(X0),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_struct_0)).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    ~spl1_2 | spl1_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f87,f81,f56])).
% 0.21/0.48  fof(f81,plain,(
% 0.21/0.48    spl1_7 <=> l1_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_7])])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | spl1_7),
% 0.21/0.48    inference(resolution,[],[f82,f42])).
% 0.21/0.48  fof(f82,plain,(
% 0.21/0.48    ~l1_struct_0(sK0) | spl1_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f81])).
% 0.21/0.48  fof(f86,plain,(
% 0.21/0.48    ~spl1_7 | spl1_8 | ~spl1_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f79,f71,f84,f81])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | ~spl1_5),
% 0.21/0.48    inference(superposition,[],[f39,f72])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ~spl1_6 | spl1_1 | ~spl1_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f74,f71,f52,f76])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    spl1_1 <=> k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0)) | (spl1_1 | ~spl1_5)),
% 0.21/0.48    inference(superposition,[],[f53,f72])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) | spl1_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f52])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    spl1_5 | ~spl1_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f69,f56,f71])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl1_2),
% 0.21/0.48    inference(resolution,[],[f68,f57])).
% 0.21/0.48  fof(f68,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 0.21/0.48    inference(resolution,[],[f38,f42])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    spl1_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f36,f64])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.48  fof(f62,plain,(
% 0.21/0.48    spl1_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f33,f60])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.21/0.48    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f18,f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.21/0.48    introduced(choice_axiom,[])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.21/0.48    inference(flattening,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.21/0.48    inference(negated_conjecture,[],[f14])).
% 0.21/0.48  fof(f14,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    spl1_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f34,f56])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ~spl1_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f35,f52])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (18805)------------------------------
% 0.21/0.48  % (18805)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (18805)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (18805)Memory used [KB]: 10746
% 0.21/0.48  % (18805)Time elapsed: 0.065 s
% 0.21/0.48  % (18805)------------------------------
% 0.21/0.48  % (18805)------------------------------
% 0.21/0.48  % (18798)Success in time 0.12 s
%------------------------------------------------------------------------------
