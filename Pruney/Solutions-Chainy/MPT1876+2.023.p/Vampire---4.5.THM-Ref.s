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
% DateTime   : Thu Dec  3 13:21:39 EST 2020

% Result     : Theorem 0.18s
% Output     : Refutation 0.18s
% Verified   : 
% Statistics : Number of formulae       :  116 ( 417 expanded)
%              Number of leaves         :   22 (  98 expanded)
%              Depth                    :   12
%              Number of atoms          :  406 (2384 expanded)
%              Number of equality atoms :   20 (  38 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f236,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f107,f171,f179,f191,f207,f211,f235])).

fof(f235,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f232])).

fof(f232,plain,
    ( $false
    | ~ spl5_1
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f103,f231])).

fof(f231,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f230,f216])).

fof(f216,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f47,f48,f50,f45,f46,f100,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | u1_struct_0(sK2(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_tdlat_3(X2)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ~ ( ! [X2] :
                  ( ( m1_pre_topc(X2,X0)
                    & v1_tdlat_3(X2)
                    & v1_pre_topc(X2)
                    & ~ v2_struct_0(X2) )
                 => u1_struct_0(X2) != X1 )
              & v2_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).

fof(f100,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl5_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v2_tex_2(X1,X0)
          <~> v1_zfmisc_1(X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          & ~ v1_xboole_0(X1) )
      & l1_pre_topc(X0)
      & v2_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
              & ~ v1_xboole_0(X1) )
           => ( v2_tex_2(X1,X0)
            <=> v1_zfmisc_1(X1) ) ) ) ),
    inference(negated_conjecture,[],[f17])).

fof(f17,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).

fof(f45,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f20])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f47,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f230,plain,
    ( v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f218,f221,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f221,plain,
    ( l1_struct_0(sK2(sK0,sK1))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f219,f68])).

fof(f68,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f219,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f50,f215,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f215,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f50,f48,f47,f45,f46,f100,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | m1_pre_topc(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f218,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f50,f49,f47,f48,f214,f212,f215,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X1)
      | v7_struct_0(X1)
      | ~ v1_tdlat_3(X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ~ v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( ~ v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( ~ v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc32_tex_2)).

fof(f212,plain,
    ( ~ v2_struct_0(sK2(sK0,sK1))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f47,f50,f48,f45,f46,f100,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f214,plain,
    ( v1_tdlat_3(sK2(sK0,sK1))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f47,f50,f48,f45,f46,f100,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK2(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f49,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f103,plain,
    ( ~ v1_zfmisc_1(sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f102,plain,
    ( spl5_2
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f211,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f208])).

fof(f208,plain,
    ( $false
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f47,f170])).

fof(f170,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f168])).

fof(f168,plain,
    ( spl5_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f207,plain,(
    spl5_6 ),
    inference(avatar_contradiction_clause,[],[f202])).

fof(f202,plain,
    ( $false
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f76,f199,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f199,plain,
    ( ~ m1_subset_1(sK4(sK1),sK1)
    | spl5_6 ),
    inference(forward_demodulation,[],[f196,f111])).

fof(f111,plain,(
    sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f47,f50,f45,f46,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(sK3(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & v1_pre_topc(X2)
              & ~ v2_struct_0(X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f196,plain,
    ( ~ m1_subset_1(sK4(sK1),u1_struct_0(sK3(sK0,sK1)))
    | spl5_6 ),
    inference(unit_resulting_resolution,[],[f50,f47,f108,f110,f190,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
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
              ( m1_subset_1(X2,u1_struct_0(X1))
             => m1_subset_1(X2,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).

fof(f190,plain,
    ( ~ m1_subset_1(sK4(sK1),u1_struct_0(sK0))
    | spl5_6 ),
    inference(avatar_component_clause,[],[f188])).

fof(f188,plain,
    ( spl5_6
  <=> m1_subset_1(sK4(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f110,plain,(
    m1_pre_topc(sK3(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f47,f50,f45,f46,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f108,plain,(
    ~ v2_struct_0(sK3(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f47,f50,f45,f46,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK3(X0,X1))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f76,plain,(
    r2_hidden(sK4(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f45,f74])).

fof(f74,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK4(X0),X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f191,plain,
    ( ~ spl5_6
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f186,f161,f102,f98,f188])).

fof(f161,plain,
    ( spl5_3
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f186,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK4(sK1),u1_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(superposition,[],[f184,f133])).

fof(f133,plain,
    ( sK1 = k1_tarski(sK4(sK1))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f45,f104,f72,f94,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_zfmisc_1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f94,plain,(
    r1_tarski(k1_tarski(sK4(sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f76,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | r1_tarski(k1_tarski(X0),X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r1_tarski(k1_tarski(X0),X1)
    <=> r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

fof(f72,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f104,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f102])).

fof(f184,plain,
    ( ! [X0] :
        ( v2_tex_2(k1_tarski(X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_3 ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,
    ( ! [X0] :
        ( v2_tex_2(k1_tarski(X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_3 ),
    inference(superposition,[],[f162,f115])).

fof(f115,plain,(
    ! [X0] :
      ( k1_tarski(X0) = k6_domain_1(u1_struct_0(sK0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f112,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X1,X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

% (4602)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f112,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f45,f46,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f162,plain,
    ( ! [X1] :
        ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f161])).

fof(f179,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f172])).

fof(f172,plain,
    ( $false
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f50,f166])).

fof(f166,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f164])).

fof(f164,plain,
    ( spl5_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f171,plain,
    ( spl5_3
    | ~ spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f82,f168,f164,f161])).

fof(f82,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0) ) ),
    inference(resolution,[],[f48,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(f107,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f44,f102,f98])).

fof(f44,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f105,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f43,f102,f98])).

fof(f43,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 13:14:07 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.18/0.43  % (4580)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.18/0.45  % (4598)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.18/0.46  % (4580)Refutation found. Thanks to Tanya!
% 0.18/0.46  % SZS status Theorem for theBenchmark
% 0.18/0.46  % (4592)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.18/0.46  % SZS output start Proof for theBenchmark
% 0.18/0.46  fof(f236,plain,(
% 0.18/0.46    $false),
% 0.18/0.46    inference(avatar_sat_refutation,[],[f105,f107,f171,f179,f191,f207,f211,f235])).
% 0.18/0.46  fof(f235,plain,(
% 0.18/0.46    ~spl5_1 | spl5_2),
% 0.18/0.46    inference(avatar_contradiction_clause,[],[f232])).
% 0.18/0.46  fof(f232,plain,(
% 0.18/0.46    $false | (~spl5_1 | spl5_2)),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f103,f231])).
% 0.18/0.46  fof(f231,plain,(
% 0.18/0.46    v1_zfmisc_1(sK1) | ~spl5_1),
% 0.18/0.46    inference(forward_demodulation,[],[f230,f216])).
% 0.18/0.46  fof(f216,plain,(
% 0.18/0.46    sK1 = u1_struct_0(sK2(sK0,sK1)) | ~spl5_1),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f47,f48,f50,f45,f46,f100,f57])).
% 0.18/0.46  fof(f57,plain,(
% 0.18/0.46    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | u1_struct_0(sK2(X0,X1)) = X1) )),
% 0.18/0.46    inference(cnf_transformation,[],[f26])).
% 0.18/0.46  fof(f26,plain,(
% 0.18/0.46    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.18/0.46    inference(flattening,[],[f25])).
% 0.18/0.46  fof(f25,plain,(
% 0.18/0.46    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.18/0.46    inference(ennf_transformation,[],[f15])).
% 0.18/0.46  fof(f15,axiom,(
% 0.18/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).
% 0.18/0.46  fof(f100,plain,(
% 0.18/0.46    v2_tex_2(sK1,sK0) | ~spl5_1),
% 0.18/0.46    inference(avatar_component_clause,[],[f98])).
% 0.18/0.46  fof(f98,plain,(
% 0.18/0.46    spl5_1 <=> v2_tex_2(sK1,sK0)),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.18/0.46  fof(f46,plain,(
% 0.18/0.46    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.18/0.46    inference(cnf_transformation,[],[f20])).
% 0.18/0.46  fof(f20,plain,(
% 0.18/0.46    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.18/0.46    inference(flattening,[],[f19])).
% 0.18/0.46  fof(f19,plain,(
% 0.18/0.46    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.18/0.46    inference(ennf_transformation,[],[f18])).
% 0.18/0.46  fof(f18,negated_conjecture,(
% 0.18/0.46    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.18/0.46    inference(negated_conjecture,[],[f17])).
% 0.18/0.46  fof(f17,conjecture,(
% 0.18/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).
% 0.18/0.46  fof(f45,plain,(
% 0.18/0.46    ~v1_xboole_0(sK1)),
% 0.18/0.46    inference(cnf_transformation,[],[f20])).
% 0.18/0.46  fof(f50,plain,(
% 0.18/0.46    l1_pre_topc(sK0)),
% 0.18/0.46    inference(cnf_transformation,[],[f20])).
% 0.18/0.46  fof(f48,plain,(
% 0.18/0.46    v2_pre_topc(sK0)),
% 0.18/0.46    inference(cnf_transformation,[],[f20])).
% 0.18/0.46  fof(f47,plain,(
% 0.18/0.46    ~v2_struct_0(sK0)),
% 0.18/0.46    inference(cnf_transformation,[],[f20])).
% 0.18/0.46  fof(f230,plain,(
% 0.18/0.46    v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1))) | ~spl5_1),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f218,f221,f51])).
% 0.18/0.46  fof(f51,plain,(
% 0.18/0.46    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f22])).
% 0.18/0.46  fof(f22,plain,(
% 0.18/0.46    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.18/0.46    inference(flattening,[],[f21])).
% 0.18/0.46  fof(f21,plain,(
% 0.18/0.46    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.18/0.46    inference(ennf_transformation,[],[f8])).
% 0.18/0.46  fof(f8,axiom,(
% 0.18/0.46    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.18/0.46  fof(f221,plain,(
% 0.18/0.46    l1_struct_0(sK2(sK0,sK1)) | ~spl5_1),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f219,f68])).
% 0.18/0.46  fof(f68,plain,(
% 0.18/0.46    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f39])).
% 0.18/0.46  fof(f39,plain,(
% 0.18/0.46    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.18/0.46    inference(ennf_transformation,[],[f6])).
% 0.18/0.46  fof(f6,axiom,(
% 0.18/0.46    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.18/0.46  fof(f219,plain,(
% 0.18/0.46    l1_pre_topc(sK2(sK0,sK1)) | ~spl5_1),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f50,f215,f65])).
% 0.18/0.46  fof(f65,plain,(
% 0.18/0.46    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f34])).
% 0.18/0.46  fof(f34,plain,(
% 0.18/0.46    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.18/0.46    inference(ennf_transformation,[],[f7])).
% 0.18/0.46  fof(f7,axiom,(
% 0.18/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.18/0.46  fof(f215,plain,(
% 0.18/0.46    m1_pre_topc(sK2(sK0,sK1),sK0) | ~spl5_1),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f50,f48,f47,f45,f46,f100,f56])).
% 0.18/0.46  fof(f56,plain,(
% 0.18/0.46    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | m1_pre_topc(sK2(X0,X1),X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f26])).
% 0.18/0.46  fof(f218,plain,(
% 0.18/0.46    v7_struct_0(sK2(sK0,sK1)) | ~spl5_1),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f50,f49,f47,f48,f214,f212,f215,f66])).
% 0.18/0.46  fof(f66,plain,(
% 0.18/0.46    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | v7_struct_0(X1) | ~v1_tdlat_3(X1)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f36])).
% 0.18/0.46  fof(f36,plain,(
% 0.18/0.46    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.18/0.46    inference(flattening,[],[f35])).
% 0.18/0.46  fof(f35,plain,(
% 0.18/0.46    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.18/0.46    inference(ennf_transformation,[],[f12])).
% 0.18/0.46  fof(f12,axiom,(
% 0.18/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc32_tex_2)).
% 0.18/0.46  fof(f212,plain,(
% 0.18/0.46    ~v2_struct_0(sK2(sK0,sK1)) | ~spl5_1),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f47,f50,f48,f45,f46,f100,f53])).
% 0.18/0.46  fof(f53,plain,(
% 0.18/0.46    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v2_struct_0(X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f26])).
% 0.18/0.46  fof(f214,plain,(
% 0.18/0.46    v1_tdlat_3(sK2(sK0,sK1)) | ~spl5_1),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f47,f50,f48,f45,f46,f100,f55])).
% 0.18/0.46  fof(f55,plain,(
% 0.18/0.46    ( ! [X0,X1] : (v1_tdlat_3(sK2(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v2_struct_0(X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f26])).
% 0.18/0.46  fof(f49,plain,(
% 0.18/0.46    v2_tdlat_3(sK0)),
% 0.18/0.46    inference(cnf_transformation,[],[f20])).
% 0.18/0.46  fof(f103,plain,(
% 0.18/0.46    ~v1_zfmisc_1(sK1) | spl5_2),
% 0.18/0.46    inference(avatar_component_clause,[],[f102])).
% 0.18/0.46  fof(f102,plain,(
% 0.18/0.46    spl5_2 <=> v1_zfmisc_1(sK1)),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.18/0.46  fof(f211,plain,(
% 0.18/0.46    ~spl5_5),
% 0.18/0.46    inference(avatar_contradiction_clause,[],[f208])).
% 0.18/0.46  fof(f208,plain,(
% 0.18/0.46    $false | ~spl5_5),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f47,f170])).
% 0.18/0.46  fof(f170,plain,(
% 0.18/0.46    v2_struct_0(sK0) | ~spl5_5),
% 0.18/0.46    inference(avatar_component_clause,[],[f168])).
% 0.18/0.46  fof(f168,plain,(
% 0.18/0.46    spl5_5 <=> v2_struct_0(sK0)),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.18/0.46  fof(f207,plain,(
% 0.18/0.46    spl5_6),
% 0.18/0.46    inference(avatar_contradiction_clause,[],[f202])).
% 0.18/0.46  fof(f202,plain,(
% 0.18/0.46    $false | spl5_6),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f76,f199,f73])).
% 0.18/0.46  fof(f73,plain,(
% 0.18/0.46    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f42])).
% 0.18/0.46  fof(f42,plain,(
% 0.18/0.46    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 0.18/0.46    inference(ennf_transformation,[],[f5])).
% 0.18/0.46  fof(f5,axiom,(
% 0.18/0.46    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 0.18/0.46  fof(f199,plain,(
% 0.18/0.46    ~m1_subset_1(sK4(sK1),sK1) | spl5_6),
% 0.18/0.46    inference(forward_demodulation,[],[f196,f111])).
% 0.18/0.46  fof(f111,plain,(
% 0.18/0.46    sK1 = u1_struct_0(sK3(sK0,sK1))),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f47,f50,f45,f46,f64])).
% 0.18/0.46  fof(f64,plain,(
% 0.18/0.46    ( ! [X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK3(X0,X1)) = X1) )),
% 0.18/0.46    inference(cnf_transformation,[],[f33])).
% 0.18/0.46  fof(f33,plain,(
% 0.18/0.46    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.18/0.46    inference(flattening,[],[f32])).
% 0.18/0.46  fof(f32,plain,(
% 0.18/0.46    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.18/0.46    inference(ennf_transformation,[],[f13])).
% 0.18/0.46  fof(f13,axiom,(
% 0.18/0.46    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).
% 0.18/0.46  fof(f196,plain,(
% 0.18/0.46    ~m1_subset_1(sK4(sK1),u1_struct_0(sK3(sK0,sK1))) | spl5_6),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f50,f47,f108,f110,f190,f59])).
% 0.18/0.46  fof(f59,plain,(
% 0.18/0.46    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0))) )),
% 0.18/0.46    inference(cnf_transformation,[],[f30])).
% 0.18/0.46  fof(f30,plain,(
% 0.18/0.46    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.18/0.46    inference(flattening,[],[f29])).
% 0.18/0.46  fof(f29,plain,(
% 0.18/0.46    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.18/0.46    inference(ennf_transformation,[],[f9])).
% 0.18/0.46  fof(f9,axiom,(
% 0.18/0.46    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).
% 0.18/0.46  fof(f190,plain,(
% 0.18/0.46    ~m1_subset_1(sK4(sK1),u1_struct_0(sK0)) | spl5_6),
% 0.18/0.46    inference(avatar_component_clause,[],[f188])).
% 0.18/0.46  fof(f188,plain,(
% 0.18/0.46    spl5_6 <=> m1_subset_1(sK4(sK1),u1_struct_0(sK0))),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.18/0.46  fof(f110,plain,(
% 0.18/0.46    m1_pre_topc(sK3(sK0,sK1),sK0)),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f47,f50,f45,f46,f63])).
% 0.18/0.46  fof(f63,plain,(
% 0.18/0.46    ( ! [X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(sK3(X0,X1),X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f33])).
% 0.18/0.46  fof(f108,plain,(
% 0.18/0.46    ~v2_struct_0(sK3(sK0,sK1))),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f47,f50,f45,f46,f61])).
% 0.18/0.46  fof(f61,plain,(
% 0.18/0.46    ( ! [X0,X1] : (~v2_struct_0(sK3(X0,X1)) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f33])).
% 0.18/0.46  fof(f76,plain,(
% 0.18/0.46    r2_hidden(sK4(sK1),sK1)),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f45,f74])).
% 0.18/0.46  fof(f74,plain,(
% 0.18/0.46    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK4(X0),X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f1])).
% 0.18/0.46  fof(f1,axiom,(
% 0.18/0.46    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 0.18/0.46  fof(f191,plain,(
% 0.18/0.46    ~spl5_6 | spl5_1 | ~spl5_2 | ~spl5_3),
% 0.18/0.46    inference(avatar_split_clause,[],[f186,f161,f102,f98,f188])).
% 0.18/0.46  fof(f161,plain,(
% 0.18/0.46    spl5_3 <=> ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0))),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.18/0.46  fof(f186,plain,(
% 0.18/0.46    v2_tex_2(sK1,sK0) | ~m1_subset_1(sK4(sK1),u1_struct_0(sK0)) | (~spl5_2 | ~spl5_3)),
% 0.18/0.46    inference(superposition,[],[f184,f133])).
% 0.18/0.46  fof(f133,plain,(
% 0.18/0.46    sK1 = k1_tarski(sK4(sK1)) | ~spl5_2),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f45,f104,f72,f94,f52])).
% 0.18/0.46  fof(f52,plain,(
% 0.18/0.46    ( ! [X0,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.18/0.46    inference(cnf_transformation,[],[f24])).
% 0.18/0.46  fof(f24,plain,(
% 0.18/0.46    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.18/0.46    inference(flattening,[],[f23])).
% 0.18/0.46  fof(f23,plain,(
% 0.18/0.46    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.18/0.46    inference(ennf_transformation,[],[f14])).
% 0.18/0.46  fof(f14,axiom,(
% 0.18/0.46    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 0.18/0.46  fof(f94,plain,(
% 0.18/0.46    r1_tarski(k1_tarski(sK4(sK1)),sK1)),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f76,f70])).
% 0.18/0.46  fof(f70,plain,(
% 0.18/0.46    ( ! [X0,X1] : (~r2_hidden(X0,X1) | r1_tarski(k1_tarski(X0),X1)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f3])).
% 0.18/0.46  fof(f3,axiom,(
% 0.18/0.46    ! [X0,X1] : (r1_tarski(k1_tarski(X0),X1) <=> r2_hidden(X0,X1))),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).
% 0.18/0.46  fof(f72,plain,(
% 0.18/0.46    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 0.18/0.46    inference(cnf_transformation,[],[f2])).
% 0.18/0.46  fof(f2,axiom,(
% 0.18/0.46    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 0.18/0.46  fof(f104,plain,(
% 0.18/0.46    v1_zfmisc_1(sK1) | ~spl5_2),
% 0.18/0.46    inference(avatar_component_clause,[],[f102])).
% 0.18/0.46  fof(f184,plain,(
% 0.18/0.46    ( ! [X0] : (v2_tex_2(k1_tarski(X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl5_3),
% 0.18/0.46    inference(duplicate_literal_removal,[],[f183])).
% 0.18/0.46  fof(f183,plain,(
% 0.18/0.46    ( ! [X0] : (v2_tex_2(k1_tarski(X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl5_3),
% 0.18/0.46    inference(superposition,[],[f162,f115])).
% 0.18/0.46  fof(f115,plain,(
% 0.18/0.46    ( ! [X0] : (k1_tarski(X0) = k6_domain_1(u1_struct_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 0.18/0.46    inference(resolution,[],[f112,f69])).
% 0.18/0.46  fof(f69,plain,(
% 0.18/0.46    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f41])).
% 0.18/0.46  fof(f41,plain,(
% 0.18/0.46    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.18/0.46    inference(flattening,[],[f40])).
% 0.18/0.46  fof(f40,plain,(
% 0.18/0.46    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.18/0.46    inference(ennf_transformation,[],[f10])).
% 0.18/0.46  % (4602)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.18/0.46  fof(f10,axiom,(
% 0.18/0.46    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.18/0.46  fof(f112,plain,(
% 0.18/0.46    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f45,f46,f60])).
% 0.18/0.46  fof(f60,plain,(
% 0.18/0.46    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f31])).
% 0.18/0.46  fof(f31,plain,(
% 0.18/0.46    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.18/0.46    inference(ennf_transformation,[],[f4])).
% 0.18/0.46  fof(f4,axiom,(
% 0.18/0.46    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.18/0.46  fof(f162,plain,(
% 0.18/0.46    ( ! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl5_3),
% 0.18/0.46    inference(avatar_component_clause,[],[f161])).
% 0.18/0.46  fof(f179,plain,(
% 0.18/0.46    spl5_4),
% 0.18/0.46    inference(avatar_contradiction_clause,[],[f172])).
% 0.18/0.46  fof(f172,plain,(
% 0.18/0.46    $false | spl5_4),
% 0.18/0.46    inference(unit_resulting_resolution,[],[f50,f166])).
% 0.18/0.46  fof(f166,plain,(
% 0.18/0.46    ~l1_pre_topc(sK0) | spl5_4),
% 0.18/0.46    inference(avatar_component_clause,[],[f164])).
% 0.18/0.46  fof(f164,plain,(
% 0.18/0.46    spl5_4 <=> l1_pre_topc(sK0)),
% 0.18/0.46    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.18/0.46  fof(f171,plain,(
% 0.18/0.46    spl5_3 | ~spl5_4 | spl5_5),
% 0.18/0.46    inference(avatar_split_clause,[],[f82,f168,f164,f161])).
% 0.18/0.46  fof(f82,plain,(
% 0.18/0.46    ( ! [X1] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0)) )),
% 0.18/0.46    inference(resolution,[],[f48,f58])).
% 0.18/0.46  fof(f58,plain,(
% 0.18/0.46    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)) )),
% 0.18/0.46    inference(cnf_transformation,[],[f28])).
% 0.18/0.46  fof(f28,plain,(
% 0.18/0.46    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.18/0.46    inference(flattening,[],[f27])).
% 0.18/0.46  fof(f27,plain,(
% 0.18/0.46    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.18/0.46    inference(ennf_transformation,[],[f16])).
% 0.18/0.46  fof(f16,axiom,(
% 0.18/0.46    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.18/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).
% 0.18/0.46  fof(f107,plain,(
% 0.18/0.46    ~spl5_1 | ~spl5_2),
% 0.18/0.46    inference(avatar_split_clause,[],[f44,f102,f98])).
% 0.18/0.46  fof(f44,plain,(
% 0.18/0.46    ~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 0.18/0.46    inference(cnf_transformation,[],[f20])).
% 0.18/0.46  fof(f105,plain,(
% 0.18/0.46    spl5_1 | spl5_2),
% 0.18/0.46    inference(avatar_split_clause,[],[f43,f102,f98])).
% 0.18/0.46  fof(f43,plain,(
% 0.18/0.46    v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 0.18/0.46    inference(cnf_transformation,[],[f20])).
% 0.18/0.46  % SZS output end Proof for theBenchmark
% 0.18/0.46  % (4580)------------------------------
% 0.18/0.46  % (4580)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.18/0.46  % (4580)Termination reason: Refutation
% 0.18/0.46  
% 0.18/0.46  % (4580)Memory used [KB]: 6396
% 0.18/0.46  % (4580)Time elapsed: 0.093 s
% 0.18/0.46  % (4580)------------------------------
% 0.18/0.46  % (4580)------------------------------
% 0.18/0.47  % (4573)Success in time 0.121 s
%------------------------------------------------------------------------------
