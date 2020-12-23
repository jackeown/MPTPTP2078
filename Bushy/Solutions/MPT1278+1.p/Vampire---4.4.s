%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : tops_1__t97_tops_1.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:39:35 EDT 2019

% Result     : Theorem 0.19s
% Output     : Refutation 0.19s
% Verified   : 
% Statistics : Number of formulae       :   73 ( 120 expanded)
%              Number of leaves         :   16 (  43 expanded)
%              Depth                    :   13
%              Number of atoms          :  253 ( 427 expanded)
%              Number of equality atoms :   22 (  45 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f258,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f84,f88,f92,f96,f100,f104,f131,f135,f173,f208,f257])).

fof(f257,plain,
    ( ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | spl5_9
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_34 ),
    inference(avatar_contradiction_clause,[],[f256])).

fof(f256,plain,
    ( $false
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_10
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_34 ),
    inference(subsumption_resolution,[],[f255,f103])).

fof(f103,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_10 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl5_10
  <=> m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f255,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_4
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_34 ),
    inference(subsumption_resolution,[],[f254,f91])).

fof(f91,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f90])).

fof(f90,plain,
    ( spl5_4
  <=> v3_pre_topc(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f254,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_9
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_34 ),
    inference(subsumption_resolution,[],[f253,f99])).

fof(f99,plain,
    ( k1_xboole_0 != sK1
    | ~ spl5_9 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl5_9
  <=> k1_xboole_0 != sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_9])])).

fof(f253,plain,
    ( k1_xboole_0 = sK1
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_14
    | ~ spl5_34 ),
    inference(resolution,[],[f160,f207])).

fof(f207,plain,
    ( r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK1)
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl5_34
  <=> r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f160,plain,
    ( ! [X0] :
        ( ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X0)
        | k1_xboole_0 = X0
        | ~ v3_pre_topc(X0,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) )
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_12
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f159,f130])).

fof(f130,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_12 ),
    inference(avatar_component_clause,[],[f129])).

fof(f129,plain,
    ( spl5_12
  <=> v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_12])])).

fof(f159,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X0)
        | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) )
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f158,f83])).

fof(f83,plain,
    ( v2_pre_topc(sK0)
    | ~ spl5_0 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl5_0
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_0])])).

fof(f158,plain,
    ( ! [X0] :
        ( ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X0)
        | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) )
    | ~ spl5_2
    | ~ spl5_14 ),
    inference(subsumption_resolution,[],[f148,f87])).

fof(f87,plain,
    ( l1_pre_topc(sK0)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl5_2
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f148,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(sK0)
        | ~ v2_pre_topc(sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k1_xboole_0 = X0
        | ~ v3_pre_topc(X0,sK0)
        | ~ r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),X0)
        | ~ v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0) )
    | ~ spl5_14 ),
    inference(resolution,[],[f134,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | k1_xboole_0 = X2
      | ~ v3_pre_topc(X2,X0)
      | ~ r1_xboole_0(X1,X2)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> ! [X2] :
                ( ~ r1_xboole_0(X1,X2)
                | ~ v3_pre_topc(X2,X0)
                | k1_xboole_0 = X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f29])).

fof(f29,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ~ ( r1_xboole_0(X1,X2)
                    & v3_pre_topc(X2,X0)
                    & k1_xboole_0 != X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t97_tops_1.p',t80_tops_1)).

fof(f134,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_14 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl5_14
  <=> m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f208,plain,
    ( spl5_34
    | ~ spl5_24 ),
    inference(avatar_split_clause,[],[f191,f171,f206])).

fof(f171,plain,
    ( spl5_24
  <=> k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_24])])).

fof(f191,plain,
    ( r1_xboole_0(k3_subset_1(u1_struct_0(sK0),sK1),sK1)
    | ~ spl5_24 ),
    inference(superposition,[],[f77,f172])).

fof(f172,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl5_24 ),
    inference(avatar_component_clause,[],[f171])).

fof(f77,plain,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0,X1] : r1_xboole_0(k4_xboole_0(X0,X1),X1) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t97_tops_1.p',t79_xboole_1)).

fof(f173,plain,
    ( spl5_24
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f113,f102,f171])).

fof(f113,plain,
    ( k3_subset_1(u1_struct_0(sK0),sK1) = k4_xboole_0(u1_struct_0(sK0),sK1)
    | ~ spl5_10 ),
    inference(resolution,[],[f103,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( k3_subset_1(X0,X1) = k4_xboole_0(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k3_subset_1(X0,X1) = k4_xboole_0(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t97_tops_1.p',d5_subset_1)).

fof(f135,plain,
    ( spl5_14
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f111,f102,f133])).

fof(f111,plain,
    ( m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl5_10 ),
    inference(resolution,[],[f103,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t97_tops_1.p',dt_k3_subset_1)).

fof(f131,plain,
    ( spl5_12
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(avatar_split_clause,[],[f127,f102,f94,f86,f82,f129])).

fof(f94,plain,
    ( spl5_6
  <=> v3_tops_1(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f127,plain,
    ( v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_0
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f126,f83])).

fof(f126,plain,
    ( ~ v2_pre_topc(sK0)
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_2
    | ~ spl5_6
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f125,f95])).

fof(f95,plain,
    ( v3_tops_1(sK1,sK0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f94])).

fof(f125,plain,
    ( ~ v3_tops_1(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_2
    | ~ spl5_10 ),
    inference(subsumption_resolution,[],[f110,f87])).

fof(f110,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v3_tops_1(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | v1_tops_1(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ spl5_10 ),
    inference(resolution,[],[f103,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_tops_1(X1,X0)
      | ~ v2_pre_topc(X0)
      | v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tops_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tops_1(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & v3_tops_1(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v1_tops_1(k3_subset_1(u1_struct_0(X0),X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t97_tops_1.p',fc15_tops_1)).

fof(f104,plain,(
    spl5_10 ),
    inference(avatar_split_clause,[],[f52,f102])).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ? [X0] :
      ( ? [X1] :
          ( k1_xboole_0 != X1
          & v3_tops_1(X1,X0)
          & v3_pre_topc(X1,X0)
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( ( v3_tops_1(X1,X0)
                & v3_pre_topc(X1,X0) )
             => k1_xboole_0 = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tops_1(X1,X0)
              & v3_pre_topc(X1,X0) )
           => k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/tops_1__t97_tops_1.p',t97_tops_1)).

fof(f100,plain,(
    ~ spl5_9 ),
    inference(avatar_split_clause,[],[f55,f98])).

fof(f55,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f33])).

fof(f96,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f54,f94])).

fof(f54,plain,(
    v3_tops_1(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f92,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f53,f90])).

fof(f53,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f88,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f57,f86])).

fof(f57,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).

fof(f84,plain,(
    spl5_0 ),
    inference(avatar_split_clause,[],[f56,f82])).

fof(f56,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f33])).
%------------------------------------------------------------------------------
