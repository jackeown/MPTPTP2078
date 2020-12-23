%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:10:58 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  139 ( 217 expanded)
%              Number of leaves         :   39 (  96 expanded)
%              Depth                    :    8
%              Number of atoms          :  374 ( 570 expanded)
%              Number of equality atoms :   79 ( 127 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f205,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f61,f66,f71,f75,f79,f83,f91,f95,f100,f104,f109,f113,f125,f133,f137,f143,f150,f154,f159,f166,f191,f196,f204])).

fof(f204,plain,
    ( ~ spl1_6
    | ~ spl1_8
    | spl1_15
    | ~ spl1_16
    | ~ spl1_22
    | ~ spl1_28 ),
    inference(avatar_contradiction_clause,[],[f203])).

fof(f203,plain,
    ( $false
    | ~ spl1_6
    | ~ spl1_8
    | spl1_15
    | ~ spl1_16
    | ~ spl1_22
    | ~ spl1_28 ),
    inference(subsumption_resolution,[],[f202,f124])).

fof(f124,plain,
    ( u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0))
    | spl1_15 ),
    inference(avatar_component_clause,[],[f122])).

fof(f122,plain,
    ( spl1_15
  <=> u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).

fof(f202,plain,
    ( u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))
    | ~ spl1_6
    | ~ spl1_8
    | ~ spl1_16
    | ~ spl1_22
    | ~ spl1_28 ),
    inference(forward_demodulation,[],[f201,f90])).

fof(f90,plain,
    ( ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0
    | ~ spl1_8 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl1_8
  <=> ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).

fof(f201,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0)
    | ~ spl1_6
    | ~ spl1_16
    | ~ spl1_22
    | ~ spl1_28 ),
    inference(forward_demodulation,[],[f200,f165])).

fof(f165,plain,
    ( k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)
    | ~ spl1_22 ),
    inference(avatar_component_clause,[],[f163])).

fof(f163,plain,
    ( spl1_22
  <=> k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).

fof(f200,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0))
    | ~ spl1_6
    | ~ spl1_16
    | ~ spl1_28 ),
    inference(forward_demodulation,[],[f198,f132])).

fof(f132,plain,
    ( ! [X1] : k1_xboole_0 = k3_subset_1(X1,X1)
    | ~ spl1_16 ),
    inference(avatar_component_clause,[],[f131])).

fof(f131,plain,
    ( spl1_16
  <=> ! [X1] : k1_xboole_0 = k3_subset_1(X1,X1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).

fof(f198,plain,
    ( k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0))))
    | ~ spl1_6
    | ~ spl1_28 ),
    inference(resolution,[],[f195,f82])).

fof(f82,plain,
    ( ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))
    | ~ spl1_6 ),
    inference(avatar_component_clause,[],[f81])).

fof(f81,plain,
    ( spl1_6
  <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).

fof(f195,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) )
    | ~ spl1_28 ),
    inference(avatar_component_clause,[],[f194])).

fof(f194,plain,
    ( spl1_28
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_28])])).

fof(f196,plain,
    ( spl1_28
    | ~ spl1_2
    | ~ spl1_27 ),
    inference(avatar_split_clause,[],[f192,f189,f63,f194])).

fof(f63,plain,
    ( spl1_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).

fof(f189,plain,
    ( spl1_27
  <=> ! [X1,X0] :
        ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_27])])).

fof(f192,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))) )
    | ~ spl1_2
    | ~ spl1_27 ),
    inference(resolution,[],[f190,f65])).

fof(f65,plain,
    ( l1_pre_topc(sK0)
    | ~ spl1_2 ),
    inference(avatar_component_clause,[],[f63])).

fof(f190,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) )
    | ~ spl1_27 ),
    inference(avatar_component_clause,[],[f189])).

fof(f191,plain,(
    spl1_27 ),
    inference(avatar_split_clause,[],[f45,f189])).

fof(f45,plain,(
    ! [X0,X1] :
      ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).

fof(f166,plain,
    ( spl1_22
    | ~ spl1_4
    | ~ spl1_19
    | ~ spl1_21 ),
    inference(avatar_split_clause,[],[f161,f157,f147,f73,f163])).

fof(f73,plain,
    ( spl1_4
  <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).

fof(f147,plain,
    ( spl1_19
  <=> v4_pre_topc(k1_xboole_0,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).

fof(f157,plain,
    ( spl1_21
  <=> ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).

fof(f161,plain,
    ( k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)
    | ~ spl1_4
    | ~ spl1_19
    | ~ spl1_21 ),
    inference(subsumption_resolution,[],[f160,f74])).

fof(f74,plain,
    ( ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))
    | ~ spl1_4 ),
    inference(avatar_component_clause,[],[f73])).

fof(f160,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)
    | ~ spl1_19
    | ~ spl1_21 ),
    inference(resolution,[],[f158,f149])).

fof(f149,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl1_19 ),
    inference(avatar_component_clause,[],[f147])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl1_21 ),
    inference(avatar_component_clause,[],[f157])).

fof(f159,plain,
    ( spl1_21
    | ~ spl1_2
    | ~ spl1_20 ),
    inference(avatar_split_clause,[],[f155,f152,f63,f157])).

fof(f152,plain,
    ( spl1_20
  <=> ! [X1,X0] :
        ( k2_pre_topc(X0,X1) = X1
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).

fof(f155,plain,
    ( ! [X0] :
        ( ~ v4_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k2_pre_topc(sK0,X0) = X0 )
    | ~ spl1_2
    | ~ spl1_20 ),
    inference(resolution,[],[f153,f65])).

fof(f153,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v4_pre_topc(X1,X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | k2_pre_topc(X0,X1) = X1 )
    | ~ spl1_20 ),
    inference(avatar_component_clause,[],[f152])).

fof(f154,plain,(
    spl1_20 ),
    inference(avatar_split_clause,[],[f46,f152])).

fof(f46,plain,(
    ! [X0,X1] :
      ( k2_pre_topc(X0,X1) = X1
      | ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f150,plain,
    ( spl1_19
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_18 ),
    inference(avatar_split_clause,[],[f145,f141,f73,f68,f147])).

fof(f68,plain,
    ( spl1_3
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).

fof(f141,plain,
    ( spl1_18
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).

fof(f145,plain,
    ( v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl1_3
    | ~ spl1_4
    | ~ spl1_18 ),
    inference(subsumption_resolution,[],[f144,f74])).

fof(f144,plain,
    ( ~ m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(k1_xboole_0,sK0)
    | ~ spl1_3
    | ~ spl1_18 ),
    inference(resolution,[],[f142,f70])).

fof(f70,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl1_3 ),
    inference(avatar_component_clause,[],[f68])).

fof(f142,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl1_18 ),
    inference(avatar_component_clause,[],[f141])).

fof(f143,plain,
    ( spl1_18
    | ~ spl1_1
    | ~ spl1_2
    | ~ spl1_17 ),
    inference(avatar_split_clause,[],[f139,f135,f63,f58,f141])).

fof(f58,plain,
    ( spl1_1
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).

fof(f135,plain,
    ( spl1_17
  <=> ! [X1,X0] :
        ( v4_pre_topc(X1,X0)
        | ~ v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ l1_pre_topc(X0)
        | ~ v2_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).

fof(f139,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0) )
    | ~ spl1_1
    | ~ spl1_2
    | ~ spl1_17 ),
    inference(subsumption_resolution,[],[f138,f60])).

fof(f60,plain,
    ( v2_pre_topc(sK0)
    | ~ spl1_1 ),
    inference(avatar_component_clause,[],[f58])).

fof(f138,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | v4_pre_topc(X0,sK0)
        | ~ v2_pre_topc(sK0) )
    | ~ spl1_2
    | ~ spl1_17 ),
    inference(resolution,[],[f136,f65])).

fof(f136,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X0)
        | ~ v1_xboole_0(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        | v4_pre_topc(X1,X0)
        | ~ v2_pre_topc(X0) )
    | ~ spl1_17 ),
    inference(avatar_component_clause,[],[f135])).

fof(f137,plain,(
    spl1_17 ),
    inference(avatar_split_clause,[],[f48,f135])).

fof(f48,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(X1,X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v4_pre_topc(X1,X0)
          | ~ v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_xboole_0(X1)
           => v4_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).

fof(f133,plain,
    ( spl1_16
    | ~ spl1_6
    | ~ spl1_9
    | ~ spl1_12 ),
    inference(avatar_split_clause,[],[f129,f107,f93,f81,f131])).

fof(f93,plain,
    ( spl1_9
  <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).

fof(f107,plain,
    ( spl1_12
  <=> ! [X1,X0] :
        ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).

fof(f129,plain,
    ( ! [X1] : k1_xboole_0 = k3_subset_1(X1,X1)
    | ~ spl1_6
    | ~ spl1_9
    | ~ spl1_12 ),
    inference(forward_demodulation,[],[f127,f94])).

fof(f94,plain,
    ( ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)
    | ~ spl1_9 ),
    inference(avatar_component_clause,[],[f93])).

fof(f127,plain,
    ( ! [X1] : k4_xboole_0(X1,X1) = k3_subset_1(X1,X1)
    | ~ spl1_6
    | ~ spl1_12 ),
    inference(resolution,[],[f108,f82])).

fof(f108,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) )
    | ~ spl1_12 ),
    inference(avatar_component_clause,[],[f107])).

fof(f125,plain,
    ( ~ spl1_15
    | ~ spl1_2
    | spl1_10
    | ~ spl1_13 ),
    inference(avatar_split_clause,[],[f115,f111,f97,f63,f122])).

fof(f97,plain,
    ( spl1_10
  <=> k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).

fof(f111,plain,
    ( spl1_13
  <=> ! [X0] :
        ( u1_struct_0(X0) = k2_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).

fof(f115,plain,
    ( u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0))
    | ~ spl1_2
    | spl1_10
    | ~ spl1_13 ),
    inference(backward_demodulation,[],[f99,f114])).

fof(f114,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl1_2
    | ~ spl1_13 ),
    inference(resolution,[],[f112,f65])).

fof(f112,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | u1_struct_0(X0) = k2_struct_0(X0) )
    | ~ spl1_13 ),
    inference(avatar_component_clause,[],[f111])).

fof(f99,plain,
    ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
    | spl1_10 ),
    inference(avatar_component_clause,[],[f97])).

fof(f113,plain,
    ( spl1_13
    | ~ spl1_5
    | ~ spl1_11 ),
    inference(avatar_split_clause,[],[f105,f102,f77,f111])).

fof(f77,plain,
    ( spl1_5
  <=> ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).

fof(f102,plain,
    ( spl1_11
  <=> ! [X0] :
        ( u1_struct_0(X0) = k2_struct_0(X0)
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).

fof(f105,plain,
    ( ! [X0] :
        ( u1_struct_0(X0) = k2_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl1_5
    | ~ spl1_11 ),
    inference(resolution,[],[f103,f78])).

fof(f78,plain,
    ( ! [X0] :
        ( l1_struct_0(X0)
        | ~ l1_pre_topc(X0) )
    | ~ spl1_5 ),
    inference(avatar_component_clause,[],[f77])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | u1_struct_0(X0) = k2_struct_0(X0) )
    | ~ spl1_11 ),
    inference(avatar_component_clause,[],[f102])).

fof(f109,plain,(
    spl1_12 ),
    inference(avatar_split_clause,[],[f50,f107])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).

fof(f104,plain,(
    spl1_11 ),
    inference(avatar_split_clause,[],[f43,f102])).

fof(f43,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f100,plain,(
    ~ spl1_10 ),
    inference(avatar_split_clause,[],[f34,f97])).

fof(f34,plain,(
    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,
    ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
    & l1_pre_topc(sK0)
    & v2_pre_topc(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f30])).

fof(f30,plain,
    ( ? [X0] :
        ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
   => ( k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))
      & l1_pre_topc(sK0)
      & v2_pre_topc(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f21,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0))
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).

fof(f95,plain,(
    spl1_9 ),
    inference(avatar_split_clause,[],[f55,f93])).

fof(f55,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0) ),
    inference(backward_demodulation,[],[f53,f40])).

fof(f40,plain,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

fof(f53,plain,(
    ! [X0] : k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f39,f49])).

fof(f49,plain,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

fof(f39,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f91,plain,(
    spl1_8 ),
    inference(avatar_split_clause,[],[f52,f89])).

fof(f52,plain,(
    ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0 ),
    inference(definition_unfolding,[],[f37,f51])).

fof(f51,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0) ),
    inference(definition_unfolding,[],[f42,f36])).

fof(f36,plain,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : k1_xboole_0 = k1_subset_1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).

fof(f42,plain,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).

fof(f37,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f83,plain,(
    spl1_6 ),
    inference(avatar_split_clause,[],[f56,f81])).

fof(f56,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f54,f52])).

fof(f54,plain,(
    ! [X0] : m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0)) ),
    inference(definition_unfolding,[],[f41,f51])).

fof(f41,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f79,plain,(
    spl1_5 ),
    inference(avatar_split_clause,[],[f44,f77])).

fof(f44,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f75,plain,(
    spl1_4 ),
    inference(avatar_split_clause,[],[f38,f73])).

fof(f38,plain,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).

fof(f71,plain,(
    spl1_3 ),
    inference(avatar_split_clause,[],[f35,f68])).

fof(f35,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f66,plain,(
    spl1_2 ),
    inference(avatar_split_clause,[],[f33,f63])).

fof(f33,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).

fof(f61,plain,(
    spl1_1 ),
    inference(avatar_split_clause,[],[f32,f58])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f31])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:58:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (5835)ott+11_20_afr=on:afp=100000:afq=1.0:amm=sco:anc=all:bsr=on:irw=on:lma=on:nm=4:nwc=1.2:sac=on:sp=occurrence_294 on theBenchmark
% 0.20/0.43  % (5835)Refutation found. Thanks to Tanya!
% 0.20/0.43  % SZS status Theorem for theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f205,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(avatar_sat_refutation,[],[f61,f66,f71,f75,f79,f83,f91,f95,f100,f104,f109,f113,f125,f133,f137,f143,f150,f154,f159,f166,f191,f196,f204])).
% 0.20/0.43  fof(f204,plain,(
% 0.20/0.43    ~spl1_6 | ~spl1_8 | spl1_15 | ~spl1_16 | ~spl1_22 | ~spl1_28),
% 0.20/0.43    inference(avatar_contradiction_clause,[],[f203])).
% 0.20/0.43  fof(f203,plain,(
% 0.20/0.43    $false | (~spl1_6 | ~spl1_8 | spl1_15 | ~spl1_16 | ~spl1_22 | ~spl1_28)),
% 0.20/0.43    inference(subsumption_resolution,[],[f202,f124])).
% 0.20/0.43  fof(f124,plain,(
% 0.20/0.43    u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0)) | spl1_15),
% 0.20/0.43    inference(avatar_component_clause,[],[f122])).
% 0.20/0.43  fof(f122,plain,(
% 0.20/0.43    spl1_15 <=> u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_15])])).
% 0.20/0.43  fof(f202,plain,(
% 0.20/0.43    u1_struct_0(sK0) = k1_tops_1(sK0,u1_struct_0(sK0)) | (~spl1_6 | ~spl1_8 | ~spl1_16 | ~spl1_22 | ~spl1_28)),
% 0.20/0.43    inference(forward_demodulation,[],[f201,f90])).
% 0.20/0.43  fof(f90,plain,(
% 0.20/0.43    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) ) | ~spl1_8),
% 0.20/0.43    inference(avatar_component_clause,[],[f89])).
% 0.20/0.43  fof(f89,plain,(
% 0.20/0.43    spl1_8 <=> ! [X0] : k3_subset_1(X0,k1_xboole_0) = X0),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_8])])).
% 0.20/0.43  fof(f201,plain,(
% 0.20/0.43    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k1_xboole_0) | (~spl1_6 | ~spl1_16 | ~spl1_22 | ~spl1_28)),
% 0.20/0.43    inference(forward_demodulation,[],[f200,f165])).
% 0.20/0.43  fof(f165,plain,(
% 0.20/0.43    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) | ~spl1_22),
% 0.20/0.43    inference(avatar_component_clause,[],[f163])).
% 0.20/0.43  fof(f163,plain,(
% 0.20/0.43    spl1_22 <=> k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_22])])).
% 0.20/0.43  fof(f200,plain,(
% 0.20/0.43    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k1_xboole_0)) | (~spl1_6 | ~spl1_16 | ~spl1_28)),
% 0.20/0.43    inference(forward_demodulation,[],[f198,f132])).
% 0.20/0.43  fof(f132,plain,(
% 0.20/0.43    ( ! [X1] : (k1_xboole_0 = k3_subset_1(X1,X1)) ) | ~spl1_16),
% 0.20/0.43    inference(avatar_component_clause,[],[f131])).
% 0.20/0.43  fof(f131,plain,(
% 0.20/0.43    spl1_16 <=> ! [X1] : k1_xboole_0 = k3_subset_1(X1,X1)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_16])])).
% 0.20/0.43  fof(f198,plain,(
% 0.20/0.43    k1_tops_1(sK0,u1_struct_0(sK0)) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),u1_struct_0(sK0)))) | (~spl1_6 | ~spl1_28)),
% 0.20/0.43    inference(resolution,[],[f195,f82])).
% 0.20/0.43  fof(f82,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) ) | ~spl1_6),
% 0.20/0.43    inference(avatar_component_clause,[],[f81])).
% 0.20/0.43  fof(f81,plain,(
% 0.20/0.43    spl1_6 <=> ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_6])])).
% 0.20/0.43  fof(f195,plain,(
% 0.20/0.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) ) | ~spl1_28),
% 0.20/0.43    inference(avatar_component_clause,[],[f194])).
% 0.20/0.43  fof(f194,plain,(
% 0.20/0.43    spl1_28 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0))))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_28])])).
% 0.20/0.43  fof(f196,plain,(
% 0.20/0.43    spl1_28 | ~spl1_2 | ~spl1_27),
% 0.20/0.43    inference(avatar_split_clause,[],[f192,f189,f63,f194])).
% 0.20/0.43  fof(f63,plain,(
% 0.20/0.43    spl1_2 <=> l1_pre_topc(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_2])])).
% 0.20/0.43  fof(f189,plain,(
% 0.20/0.43    spl1_27 <=> ! [X1,X0] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_27])])).
% 0.20/0.43  fof(f192,plain,(
% 0.20/0.43    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_tops_1(sK0,X0) = k3_subset_1(u1_struct_0(sK0),k2_pre_topc(sK0,k3_subset_1(u1_struct_0(sK0),X0)))) ) | (~spl1_2 | ~spl1_27)),
% 0.20/0.43    inference(resolution,[],[f190,f65])).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    l1_pre_topc(sK0) | ~spl1_2),
% 0.20/0.43    inference(avatar_component_clause,[],[f63])).
% 0.20/0.43  fof(f190,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))) ) | ~spl1_27),
% 0.20/0.43    inference(avatar_component_clause,[],[f189])).
% 0.20/0.43  fof(f191,plain,(
% 0.20/0.43    spl1_27),
% 0.20/0.43    inference(avatar_split_clause,[],[f45,f189])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f16])).
% 0.20/0.43  fof(f16,axiom,(
% 0.20/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k1_tops_1(X0,X1) = k3_subset_1(u1_struct_0(X0),k2_pre_topc(X0,k3_subset_1(u1_struct_0(X0),X1)))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tops_1)).
% 0.20/0.43  fof(f166,plain,(
% 0.20/0.43    spl1_22 | ~spl1_4 | ~spl1_19 | ~spl1_21),
% 0.20/0.43    inference(avatar_split_clause,[],[f161,f157,f147,f73,f163])).
% 0.20/0.43  fof(f73,plain,(
% 0.20/0.43    spl1_4 <=> ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_4])])).
% 0.20/0.43  fof(f147,plain,(
% 0.20/0.43    spl1_19 <=> v4_pre_topc(k1_xboole_0,sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_19])])).
% 0.20/0.43  fof(f157,plain,(
% 0.20/0.43    spl1_21 <=> ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_21])])).
% 0.20/0.43  fof(f161,plain,(
% 0.20/0.43    k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) | (~spl1_4 | ~spl1_19 | ~spl1_21)),
% 0.20/0.43    inference(subsumption_resolution,[],[f160,f74])).
% 0.20/0.43  fof(f74,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) ) | ~spl1_4),
% 0.20/0.43    inference(avatar_component_clause,[],[f73])).
% 0.20/0.43  fof(f160,plain,(
% 0.20/0.43    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | k1_xboole_0 = k2_pre_topc(sK0,k1_xboole_0) | (~spl1_19 | ~spl1_21)),
% 0.20/0.43    inference(resolution,[],[f158,f149])).
% 0.20/0.43  fof(f149,plain,(
% 0.20/0.43    v4_pre_topc(k1_xboole_0,sK0) | ~spl1_19),
% 0.20/0.43    inference(avatar_component_clause,[],[f147])).
% 0.20/0.43  fof(f158,plain,(
% 0.20/0.43    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | ~spl1_21),
% 0.20/0.43    inference(avatar_component_clause,[],[f157])).
% 0.20/0.43  fof(f159,plain,(
% 0.20/0.43    spl1_21 | ~spl1_2 | ~spl1_20),
% 0.20/0.43    inference(avatar_split_clause,[],[f155,f152,f63,f157])).
% 0.20/0.43  fof(f152,plain,(
% 0.20/0.43    spl1_20 <=> ! [X1,X0] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_20])])).
% 0.20/0.43  fof(f155,plain,(
% 0.20/0.43    ( ! [X0] : (~v4_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,X0) = X0) ) | (~spl1_2 | ~spl1_20)),
% 0.20/0.43    inference(resolution,[],[f153,f65])).
% 0.20/0.43  fof(f153,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k2_pre_topc(X0,X1) = X1) ) | ~spl1_20),
% 0.20/0.43    inference(avatar_component_clause,[],[f152])).
% 0.20/0.43  fof(f154,plain,(
% 0.20/0.43    spl1_20),
% 0.20/0.43    inference(avatar_split_clause,[],[f46,f152])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f26])).
% 0.20/0.43  fof(f26,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(flattening,[],[f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f15])).
% 0.20/0.43  fof(f15,axiom,(
% 0.20/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.20/0.43  fof(f150,plain,(
% 0.20/0.43    spl1_19 | ~spl1_3 | ~spl1_4 | ~spl1_18),
% 0.20/0.43    inference(avatar_split_clause,[],[f145,f141,f73,f68,f147])).
% 0.20/0.43  fof(f68,plain,(
% 0.20/0.43    spl1_3 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_3])])).
% 0.20/0.43  fof(f141,plain,(
% 0.20/0.43    spl1_18 <=> ! [X0] : (~v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_18])])).
% 0.20/0.43  fof(f145,plain,(
% 0.20/0.43    v4_pre_topc(k1_xboole_0,sK0) | (~spl1_3 | ~spl1_4 | ~spl1_18)),
% 0.20/0.43    inference(subsumption_resolution,[],[f144,f74])).
% 0.20/0.43  fof(f144,plain,(
% 0.20/0.43    ~m1_subset_1(k1_xboole_0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(k1_xboole_0,sK0) | (~spl1_3 | ~spl1_18)),
% 0.20/0.43    inference(resolution,[],[f142,f70])).
% 0.20/0.43  fof(f70,plain,(
% 0.20/0.43    v1_xboole_0(k1_xboole_0) | ~spl1_3),
% 0.20/0.43    inference(avatar_component_clause,[],[f68])).
% 0.20/0.43  fof(f142,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) ) | ~spl1_18),
% 0.20/0.43    inference(avatar_component_clause,[],[f141])).
% 0.20/0.43  fof(f143,plain,(
% 0.20/0.43    spl1_18 | ~spl1_1 | ~spl1_2 | ~spl1_17),
% 0.20/0.43    inference(avatar_split_clause,[],[f139,f135,f63,f58,f141])).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    spl1_1 <=> v2_pre_topc(sK0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_1])])).
% 0.20/0.43  fof(f135,plain,(
% 0.20/0.43    spl1_17 <=> ! [X1,X0] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_17])])).
% 0.20/0.43  fof(f139,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0)) ) | (~spl1_1 | ~spl1_2 | ~spl1_17)),
% 0.20/0.43    inference(subsumption_resolution,[],[f138,f60])).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    v2_pre_topc(sK0) | ~spl1_1),
% 0.20/0.43    inference(avatar_component_clause,[],[f58])).
% 0.20/0.43  fof(f138,plain,(
% 0.20/0.43    ( ! [X0] : (~v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(X0,sK0) | ~v2_pre_topc(sK0)) ) | (~spl1_2 | ~spl1_17)),
% 0.20/0.43    inference(resolution,[],[f136,f65])).
% 0.20/0.43  fof(f136,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(X1,X0) | ~v2_pre_topc(X0)) ) | ~spl1_17),
% 0.20/0.43    inference(avatar_component_clause,[],[f135])).
% 0.20/0.43  fof(f137,plain,(
% 0.20/0.43    spl1_17),
% 0.20/0.43    inference(avatar_split_clause,[],[f48,f135])).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f28])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (v4_pre_topc(X1,X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.43    inference(flattening,[],[f27])).
% 0.20/0.43  fof(f27,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) | ~v1_xboole_0(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,axiom,(
% 0.20/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_xboole_0(X1) => v4_pre_topc(X1,X0))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_pre_topc)).
% 0.20/0.43  fof(f133,plain,(
% 0.20/0.43    spl1_16 | ~spl1_6 | ~spl1_9 | ~spl1_12),
% 0.20/0.43    inference(avatar_split_clause,[],[f129,f107,f93,f81,f131])).
% 0.20/0.43  fof(f93,plain,(
% 0.20/0.43    spl1_9 <=> ! [X0] : k1_xboole_0 = k4_xboole_0(X0,X0)),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_9])])).
% 0.20/0.43  fof(f107,plain,(
% 0.20/0.43    spl1_12 <=> ! [X1,X0] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_12])])).
% 0.20/0.43  fof(f129,plain,(
% 0.20/0.43    ( ! [X1] : (k1_xboole_0 = k3_subset_1(X1,X1)) ) | (~spl1_6 | ~spl1_9 | ~spl1_12)),
% 0.20/0.43    inference(forward_demodulation,[],[f127,f94])).
% 0.20/0.43  fof(f94,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) ) | ~spl1_9),
% 0.20/0.43    inference(avatar_component_clause,[],[f93])).
% 0.20/0.43  fof(f127,plain,(
% 0.20/0.43    ( ! [X1] : (k4_xboole_0(X1,X1) = k3_subset_1(X1,X1)) ) | (~spl1_6 | ~spl1_12)),
% 0.20/0.43    inference(resolution,[],[f108,f82])).
% 0.20/0.43  fof(f108,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k4_xboole_0(X0,X1) = k3_subset_1(X0,X1)) ) | ~spl1_12),
% 0.20/0.43    inference(avatar_component_clause,[],[f107])).
% 0.20/0.43  fof(f125,plain,(
% 0.20/0.43    ~spl1_15 | ~spl1_2 | spl1_10 | ~spl1_13),
% 0.20/0.43    inference(avatar_split_clause,[],[f115,f111,f97,f63,f122])).
% 0.20/0.43  fof(f97,plain,(
% 0.20/0.43    spl1_10 <=> k2_struct_0(sK0) = k1_tops_1(sK0,k2_struct_0(sK0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_10])])).
% 0.20/0.43  fof(f111,plain,(
% 0.20/0.43    spl1_13 <=> ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_13])])).
% 0.20/0.43  fof(f115,plain,(
% 0.20/0.43    u1_struct_0(sK0) != k1_tops_1(sK0,u1_struct_0(sK0)) | (~spl1_2 | spl1_10 | ~spl1_13)),
% 0.20/0.43    inference(backward_demodulation,[],[f99,f114])).
% 0.20/0.43  fof(f114,plain,(
% 0.20/0.43    k2_struct_0(sK0) = u1_struct_0(sK0) | (~spl1_2 | ~spl1_13)),
% 0.20/0.43    inference(resolution,[],[f112,f65])).
% 0.20/0.43  fof(f112,plain,(
% 0.20/0.43    ( ! [X0] : (~l1_pre_topc(X0) | u1_struct_0(X0) = k2_struct_0(X0)) ) | ~spl1_13),
% 0.20/0.43    inference(avatar_component_clause,[],[f111])).
% 0.20/0.43  fof(f99,plain,(
% 0.20/0.43    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) | spl1_10),
% 0.20/0.43    inference(avatar_component_clause,[],[f97])).
% 0.20/0.43  fof(f113,plain,(
% 0.20/0.43    spl1_13 | ~spl1_5 | ~spl1_11),
% 0.20/0.43    inference(avatar_split_clause,[],[f105,f102,f77,f111])).
% 0.20/0.43  fof(f77,plain,(
% 0.20/0.43    spl1_5 <=> ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_5])])).
% 0.20/0.43  fof(f102,plain,(
% 0.20/0.43    spl1_11 <=> ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.43    introduced(avatar_definition,[new_symbols(naming,[spl1_11])])).
% 0.20/0.43  fof(f105,plain,(
% 0.20/0.43    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_pre_topc(X0)) ) | (~spl1_5 | ~spl1_11)),
% 0.20/0.43    inference(resolution,[],[f103,f78])).
% 0.20/0.43  fof(f78,plain,(
% 0.20/0.43    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) ) | ~spl1_5),
% 0.20/0.43    inference(avatar_component_clause,[],[f77])).
% 0.20/0.43  fof(f103,plain,(
% 0.20/0.43    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) ) | ~spl1_11),
% 0.20/0.43    inference(avatar_component_clause,[],[f102])).
% 0.20/0.43  fof(f109,plain,(
% 0.20/0.43    spl1_12),
% 0.20/0.43    inference(avatar_split_clause,[],[f50,f107])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f29])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ! [X0,X1] : (k4_xboole_0(X0,X1) = k3_subset_1(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k4_xboole_0(X0,X1) = k3_subset_1(X0,X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_subset_1)).
% 0.20/0.43  fof(f104,plain,(
% 0.20/0.43    spl1_11),
% 0.20/0.43    inference(avatar_split_clause,[],[f43,f102])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    ( ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f22])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,axiom,(
% 0.20/0.43    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.43  fof(f100,plain,(
% 0.20/0.43    ~spl1_10),
% 0.20/0.43    inference(avatar_split_clause,[],[f34,f97])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0))),
% 0.20/0.43    inference(cnf_transformation,[],[f31])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0)),
% 0.20/0.43    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0])],[f21,f30])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0)) => (k2_struct_0(sK0) != k1_tops_1(sK0,k2_struct_0(sK0)) & l1_pre_topc(sK0) & v2_pre_topc(sK0))),
% 0.20/0.43    introduced(choice_axiom,[])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 0.20/0.43    inference(flattening,[],[f20])).
% 0.20/0.43  fof(f20,plain,(
% 0.20/0.43    ? [X0] : (k2_struct_0(X0) != k1_tops_1(X0,k2_struct_0(X0)) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f18])).
% 0.20/0.43  fof(f18,negated_conjecture,(
% 0.20/0.43    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.20/0.43    inference(negated_conjecture,[],[f17])).
% 0.20/0.43  fof(f17,conjecture,(
% 0.20/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => k2_struct_0(X0) = k1_tops_1(X0,k2_struct_0(X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tops_1)).
% 0.20/0.43  fof(f95,plain,(
% 0.20/0.43    spl1_9),
% 0.20/0.43    inference(avatar_split_clause,[],[f55,f93])).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,X0)) )),
% 0.20/0.43    inference(backward_demodulation,[],[f53,f40])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    ( ! [X0] : (k4_xboole_0(X0,k1_xboole_0) = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0] : k4_xboole_0(X0,k1_xboole_0) = X0),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k4_xboole_0(X0,k4_xboole_0(X0,k1_xboole_0))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f39,f49])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    ( ! [X0,X1] : (k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0,X1] : k4_xboole_0(X0,k4_xboole_0(X0,X1)) = k3_xboole_0(X0,X1)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f2])).
% 0.20/0.43  fof(f2,axiom,(
% 0.20/0.43    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.43  fof(f91,plain,(
% 0.20/0.43    spl1_8),
% 0.20/0.43    inference(avatar_split_clause,[],[f52,f89])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    ( ! [X0] : (k3_subset_1(X0,k1_xboole_0) = X0) )),
% 0.20/0.43    inference(definition_unfolding,[],[f37,f51])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_xboole_0)) )),
% 0.20/0.43    inference(definition_unfolding,[],[f42,f36])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ( ! [X0] : (k1_xboole_0 = k1_subset_1(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0] : k1_xboole_0 = k1_subset_1(X0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_subset_1)).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    ( ! [X0] : (k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f9])).
% 0.20/0.43  fof(f9,axiom,(
% 0.20/0.43    ! [X0] : k2_subset_1(X0) = k3_subset_1(X0,k1_subset_1(X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_subset_1)).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.20/0.43    inference(cnf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0] : k2_subset_1(X0) = X0),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.20/0.43  fof(f83,plain,(
% 0.20/0.43    spl1_6),
% 0.20/0.43    inference(avatar_split_clause,[],[f56,f81])).
% 0.20/0.43  fof(f56,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(forward_demodulation,[],[f54,f52])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(k3_subset_1(X0,k1_xboole_0),k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(definition_unfolding,[],[f41,f51])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,axiom,(
% 0.20/0.43    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.20/0.43  fof(f79,plain,(
% 0.20/0.43    spl1_5),
% 0.20/0.43    inference(avatar_split_clause,[],[f44,f77])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f23])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,axiom,(
% 0.20/0.43    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.43  fof(f75,plain,(
% 0.20/0.43    spl1_4),
% 0.20/0.43    inference(avatar_split_clause,[],[f38,f73])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ( ! [X0] : (m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,axiom,(
% 0.20/0.43    ! [X0] : m1_subset_1(k1_xboole_0,k1_zfmisc_1(X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset_1)).
% 0.20/0.43  fof(f71,plain,(
% 0.20/0.43    spl1_3),
% 0.20/0.43    inference(avatar_split_clause,[],[f35,f68])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    v1_xboole_0(k1_xboole_0)),
% 0.20/0.43    inference(cnf_transformation,[],[f1])).
% 0.20/0.43  fof(f1,axiom,(
% 0.20/0.43    v1_xboole_0(k1_xboole_0)),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.43  fof(f66,plain,(
% 0.20/0.43    spl1_2),
% 0.20/0.43    inference(avatar_split_clause,[],[f33,f63])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    l1_pre_topc(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f31])).
% 0.20/0.43  fof(f61,plain,(
% 0.20/0.43    spl1_1),
% 0.20/0.43    inference(avatar_split_clause,[],[f32,f58])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    v2_pre_topc(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f31])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (5835)------------------------------
% 0.20/0.43  % (5835)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (5835)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (5835)Memory used [KB]: 6140
% 0.20/0.43  % (5835)Time elapsed: 0.009 s
% 0.20/0.43  % (5835)------------------------------
% 0.20/0.43  % (5835)------------------------------
% 0.20/0.43  % (5827)Success in time 0.079 s
%------------------------------------------------------------------------------
