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
% DateTime   : Thu Dec  3 13:21:39 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.43s
% Verified   : 
% Statistics : Number of formulae       :  120 ( 421 expanded)
%              Number of leaves         :   23 (  99 expanded)
%              Depth                    :   12
%              Number of atoms          :  413 (2391 expanded)
%              Number of equality atoms :   20 (  38 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f314,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f106,f108,f183,f190,f213,f271,f287,f313])).

fof(f313,plain,
    ( ~ spl5_1
    | spl5_2 ),
    inference(avatar_contradiction_clause,[],[f309])).

fof(f309,plain,
    ( $false
    | ~ spl5_1
    | spl5_2 ),
    inference(unit_resulting_resolution,[],[f104,f308])).

fof(f308,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl5_1 ),
    inference(forward_demodulation,[],[f307,f292])).

fof(f292,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f49,f50,f52,f47,f48,f101,f59])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | u1_struct_0(sK2(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    inference(flattening,[],[f26])).

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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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

fof(f101,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f99])).

fof(f99,plain,
    ( spl5_1
  <=> v2_tex_2(sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f48,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
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
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
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

fof(f47,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f52,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f50,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f49,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f307,plain,
    ( v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1)))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f295,f299,f53])).

fof(f53,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f299,plain,
    ( l1_struct_0(sK2(sK0,sK1))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f296,f67])).

fof(f67,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f296,plain,
    ( l1_pre_topc(sK2(sK0,sK1))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f52,f291,f64])).

fof(f64,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f291,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f52,f50,f49,f47,f48,f101,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | m1_pre_topc(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f295,plain,
    ( v7_struct_0(sK2(sK0,sK1))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f52,f51,f49,f50,f290,f288,f291,f65])).

fof(f65,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f288,plain,
    ( ~ v2_struct_0(sK2(sK0,sK1))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f49,f52,f50,f47,f48,f101,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK2(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f290,plain,
    ( v1_tdlat_3(sK2(sK0,sK1))
    | ~ spl5_1 ),
    inference(unit_resulting_resolution,[],[f49,f52,f50,f47,f48,f101,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( v1_tdlat_3(sK2(X0,X1))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f51,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f104,plain,
    ( ~ v1_zfmisc_1(sK1)
    | spl5_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl5_2
  <=> v1_zfmisc_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f287,plain,(
    spl5_10 ),
    inference(avatar_contradiction_clause,[],[f282])).

fof(f282,plain,
    ( $false
    | spl5_10 ),
    inference(unit_resulting_resolution,[],[f79,f279,f76])).

fof(f76,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).

fof(f279,plain,
    ( ~ m1_subset_1(sK4(sK1),sK1)
    | spl5_10 ),
    inference(forward_demodulation,[],[f272,f112])).

fof(f112,plain,(
    sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f49,f52,f47,f48,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(sK3(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(flattening,[],[f42])).

fof(f42,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f272,plain,
    ( ~ m1_subset_1(sK4(sK1),u1_struct_0(sK3(sK0,sK1)))
    | spl5_10 ),
    inference(unit_resulting_resolution,[],[f52,f49,f109,f111,f270,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,u1_struct_0(X1))
      | m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f270,plain,
    ( ~ m1_subset_1(sK4(sK1),u1_struct_0(sK0))
    | spl5_10 ),
    inference(avatar_component_clause,[],[f268])).

fof(f268,plain,
    ( spl5_10
  <=> m1_subset_1(sK4(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).

fof(f111,plain,(
    m1_pre_topc(sK3(sK0,sK1),sK0) ),
    inference(unit_resulting_resolution,[],[f49,f52,f47,f48,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f109,plain,(
    ~ v2_struct_0(sK3(sK0,sK1)) ),
    inference(unit_resulting_resolution,[],[f49,f52,f47,f48,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ v2_struct_0(sK3(X0,X1))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f79,plain,(
    r2_hidden(sK4(sK1),sK1) ),
    inference(unit_resulting_resolution,[],[f47,f77])).

fof(f77,plain,(
    ! [X0] :
      ( r2_hidden(sK4(X0),X0)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
    <=> ! [X1] : ~ r2_hidden(X1,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

fof(f271,plain,
    ( ~ spl5_10
    | spl5_1
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(avatar_split_clause,[],[f266,f173,f103,f99,f268])).

fof(f173,plain,
    ( spl5_3
  <=> ! [X1] :
        ( ~ m1_subset_1(X1,u1_struct_0(sK0))
        | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f266,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK4(sK1),u1_struct_0(sK0))
    | ~ spl5_2
    | ~ spl5_3 ),
    inference(superposition,[],[f264,f143])).

fof(f143,plain,
    ( sK1 = k1_tarski(sK4(sK1))
    | ~ spl5_2 ),
    inference(unit_resulting_resolution,[],[f47,f105,f75,f139,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
      | v1_xboole_0(X1)
      | ~ v1_zfmisc_1(X1)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f139,plain,(
    r1_tarski(k1_tarski(sK4(sK1)),sK1) ),
    inference(unit_resulting_resolution,[],[f96,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f96,plain,(
    m1_subset_1(k1_tarski(sK4(sK1)),k1_zfmisc_1(sK1)) ),
    inference(unit_resulting_resolution,[],[f79,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
     => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).

fof(f75,plain,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : ~ v1_xboole_0(k1_tarski(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).

fof(f105,plain,
    ( v1_zfmisc_1(sK1)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f103])).

fof(f264,plain,
    ( ! [X0] :
        ( v2_tex_2(k1_tarski(X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_3 ),
    inference(duplicate_literal_removal,[],[f263])).

fof(f263,plain,
    ( ! [X0] :
        ( v2_tex_2(k1_tarski(X0),sK0)
        | ~ m1_subset_1(X0,u1_struct_0(sK0))
        | ~ m1_subset_1(X0,u1_struct_0(sK0)) )
    | ~ spl5_3 ),
    inference(superposition,[],[f174,f116])).

fof(f116,plain,(
    ! [X0] :
      ( k1_tarski(X0) = k6_domain_1(u1_struct_0(sK0),X0)
      | ~ m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f114,f68])).

fof(f68,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f114,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(unit_resulting_resolution,[],[f47,f48,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
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

fof(f174,plain,
    ( ! [X1] :
        ( v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0)
        | ~ m1_subset_1(X1,u1_struct_0(sK0)) )
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f173])).

fof(f213,plain,(
    ~ spl5_5 ),
    inference(avatar_contradiction_clause,[],[f210])).

fof(f210,plain,
    ( $false
    | ~ spl5_5 ),
    inference(unit_resulting_resolution,[],[f49,f182])).

fof(f182,plain,
    ( v2_struct_0(sK0)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f180])).

fof(f180,plain,
    ( spl5_5
  <=> v2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f190,plain,(
    spl5_4 ),
    inference(avatar_contradiction_clause,[],[f184])).

fof(f184,plain,
    ( $false
    | spl5_4 ),
    inference(unit_resulting_resolution,[],[f52,f178])).

fof(f178,plain,
    ( ~ l1_pre_topc(sK0)
    | spl5_4 ),
    inference(avatar_component_clause,[],[f176])).

fof(f176,plain,
    ( spl5_4
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f183,plain,
    ( spl5_3
    | ~ spl5_4
    | spl5_5 ),
    inference(avatar_split_clause,[],[f84,f180,f176,f173])).

fof(f84,plain,(
    ! [X1] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,u1_struct_0(sK0))
      | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0) ) ),
    inference(resolution,[],[f50,f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(f108,plain,
    ( ~ spl5_1
    | ~ spl5_2 ),
    inference(avatar_split_clause,[],[f46,f103,f99])).

fof(f46,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).

fof(f106,plain,
    ( spl5_1
    | spl5_2 ),
    inference(avatar_split_clause,[],[f45,f103,f99])).

fof(f45,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:56:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.54  % (30232)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.55  % (30235)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.21/0.56  % (30235)Refutation found. Thanks to Tanya!
% 0.21/0.56  % SZS status Theorem for theBenchmark
% 1.43/0.57  % (30231)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 1.43/0.57  % (30231)Refutation not found, incomplete strategy% (30231)------------------------------
% 1.43/0.57  % (30231)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.57  % (30231)Termination reason: Refutation not found, incomplete strategy
% 1.43/0.57  
% 1.43/0.57  % (30231)Memory used [KB]: 1663
% 1.43/0.57  % (30231)Time elapsed: 0.141 s
% 1.43/0.57  % (30231)------------------------------
% 1.43/0.57  % (30231)------------------------------
% 1.43/0.58  % (30245)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.43/0.58  % SZS output start Proof for theBenchmark
% 1.43/0.58  fof(f314,plain,(
% 1.43/0.58    $false),
% 1.43/0.58    inference(avatar_sat_refutation,[],[f106,f108,f183,f190,f213,f271,f287,f313])).
% 1.43/0.58  fof(f313,plain,(
% 1.43/0.58    ~spl5_1 | spl5_2),
% 1.43/0.58    inference(avatar_contradiction_clause,[],[f309])).
% 1.43/0.58  fof(f309,plain,(
% 1.43/0.58    $false | (~spl5_1 | spl5_2)),
% 1.43/0.58    inference(unit_resulting_resolution,[],[f104,f308])).
% 1.43/0.58  fof(f308,plain,(
% 1.43/0.58    v1_zfmisc_1(sK1) | ~spl5_1),
% 1.43/0.58    inference(forward_demodulation,[],[f307,f292])).
% 1.43/0.58  fof(f292,plain,(
% 1.43/0.58    sK1 = u1_struct_0(sK2(sK0,sK1)) | ~spl5_1),
% 1.43/0.58    inference(unit_resulting_resolution,[],[f49,f50,f52,f47,f48,f101,f59])).
% 1.43/0.58  fof(f59,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | u1_struct_0(sK2(X0,X1)) = X1) )),
% 1.43/0.58    inference(cnf_transformation,[],[f27])).
% 1.43/0.58  fof(f27,plain,(
% 1.43/0.58    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.43/0.58    inference(flattening,[],[f26])).
% 1.43/0.58  fof(f26,plain,(
% 1.43/0.58    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.43/0.58    inference(ennf_transformation,[],[f16])).
% 1.43/0.58  fof(f16,axiom,(
% 1.43/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).
% 1.43/0.58  fof(f101,plain,(
% 1.43/0.58    v2_tex_2(sK1,sK0) | ~spl5_1),
% 1.43/0.58    inference(avatar_component_clause,[],[f99])).
% 1.43/0.58  fof(f99,plain,(
% 1.43/0.58    spl5_1 <=> v2_tex_2(sK1,sK0)),
% 1.43/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 1.43/0.58  fof(f48,plain,(
% 1.43/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.43/0.58    inference(cnf_transformation,[],[f21])).
% 1.43/0.58  fof(f21,plain,(
% 1.43/0.58    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.43/0.58    inference(flattening,[],[f20])).
% 1.43/0.58  fof(f20,plain,(
% 1.43/0.58    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.43/0.58    inference(ennf_transformation,[],[f19])).
% 1.43/0.58  fof(f19,negated_conjecture,(
% 1.43/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.43/0.58    inference(negated_conjecture,[],[f18])).
% 1.43/0.58  fof(f18,conjecture,(
% 1.43/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).
% 1.43/0.58  fof(f47,plain,(
% 1.43/0.58    ~v1_xboole_0(sK1)),
% 1.43/0.58    inference(cnf_transformation,[],[f21])).
% 1.43/0.58  fof(f52,plain,(
% 1.43/0.58    l1_pre_topc(sK0)),
% 1.43/0.58    inference(cnf_transformation,[],[f21])).
% 1.43/0.58  fof(f50,plain,(
% 1.43/0.58    v2_pre_topc(sK0)),
% 1.43/0.58    inference(cnf_transformation,[],[f21])).
% 1.43/0.58  fof(f49,plain,(
% 1.43/0.58    ~v2_struct_0(sK0)),
% 1.43/0.58    inference(cnf_transformation,[],[f21])).
% 1.43/0.58  fof(f307,plain,(
% 1.43/0.58    v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1))) | ~spl5_1),
% 1.43/0.58    inference(unit_resulting_resolution,[],[f295,f299,f53])).
% 1.43/0.58  fof(f53,plain,(
% 1.43/0.58    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f23])).
% 1.43/0.58  fof(f23,plain,(
% 1.43/0.58    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 1.43/0.58    inference(flattening,[],[f22])).
% 1.43/0.58  fof(f22,plain,(
% 1.43/0.58    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 1.43/0.58    inference(ennf_transformation,[],[f9])).
% 1.43/0.58  fof(f9,axiom,(
% 1.43/0.58    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).
% 1.43/0.58  fof(f299,plain,(
% 1.43/0.58    l1_struct_0(sK2(sK0,sK1)) | ~spl5_1),
% 1.43/0.58    inference(unit_resulting_resolution,[],[f296,f67])).
% 1.43/0.58  fof(f67,plain,(
% 1.43/0.58    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f39])).
% 1.43/0.58  fof(f39,plain,(
% 1.43/0.58    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.43/0.58    inference(ennf_transformation,[],[f7])).
% 1.43/0.58  fof(f7,axiom,(
% 1.43/0.58    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.43/0.58  fof(f296,plain,(
% 1.43/0.58    l1_pre_topc(sK2(sK0,sK1)) | ~spl5_1),
% 1.43/0.58    inference(unit_resulting_resolution,[],[f52,f291,f64])).
% 1.43/0.58  fof(f64,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | l1_pre_topc(X1)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f34])).
% 1.43/0.58  fof(f34,plain,(
% 1.43/0.58    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.43/0.58    inference(ennf_transformation,[],[f8])).
% 1.43/0.58  fof(f8,axiom,(
% 1.43/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.43/0.58  fof(f291,plain,(
% 1.43/0.58    m1_pre_topc(sK2(sK0,sK1),sK0) | ~spl5_1),
% 1.43/0.58    inference(unit_resulting_resolution,[],[f52,f50,f49,f47,f48,f101,f58])).
% 1.43/0.58  fof(f58,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | m1_pre_topc(sK2(X0,X1),X0)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f27])).
% 1.43/0.58  fof(f295,plain,(
% 1.43/0.58    v7_struct_0(sK2(sK0,sK1)) | ~spl5_1),
% 1.43/0.58    inference(unit_resulting_resolution,[],[f52,f51,f49,f50,f290,f288,f291,f65])).
% 1.43/0.58  fof(f65,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1) | v7_struct_0(X1) | ~v1_tdlat_3(X1)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f36])).
% 1.43/0.58  fof(f36,plain,(
% 1.43/0.58    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.43/0.58    inference(flattening,[],[f35])).
% 1.43/0.58  fof(f35,plain,(
% 1.43/0.58    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.43/0.58    inference(ennf_transformation,[],[f13])).
% 1.43/0.58  fof(f13,axiom,(
% 1.43/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc32_tex_2)).
% 1.43/0.58  fof(f288,plain,(
% 1.43/0.58    ~v2_struct_0(sK2(sK0,sK1)) | ~spl5_1),
% 1.43/0.58    inference(unit_resulting_resolution,[],[f49,f52,f50,f47,f48,f101,f55])).
% 1.43/0.58  fof(f55,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~v2_struct_0(sK2(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v2_struct_0(X0)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f27])).
% 1.43/0.58  fof(f290,plain,(
% 1.43/0.58    v1_tdlat_3(sK2(sK0,sK1)) | ~spl5_1),
% 1.43/0.58    inference(unit_resulting_resolution,[],[f49,f52,f50,f47,f48,f101,f57])).
% 1.43/0.58  fof(f57,plain,(
% 1.43/0.58    ( ! [X0,X1] : (v1_tdlat_3(sK2(X0,X1)) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v2_struct_0(X0)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f27])).
% 1.43/0.58  fof(f51,plain,(
% 1.43/0.58    v2_tdlat_3(sK0)),
% 1.43/0.58    inference(cnf_transformation,[],[f21])).
% 1.43/0.58  fof(f104,plain,(
% 1.43/0.58    ~v1_zfmisc_1(sK1) | spl5_2),
% 1.43/0.58    inference(avatar_component_clause,[],[f103])).
% 1.43/0.58  fof(f103,plain,(
% 1.43/0.58    spl5_2 <=> v1_zfmisc_1(sK1)),
% 1.43/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 1.43/0.58  fof(f287,plain,(
% 1.43/0.58    spl5_10),
% 1.43/0.58    inference(avatar_contradiction_clause,[],[f282])).
% 1.43/0.58  fof(f282,plain,(
% 1.43/0.58    $false | spl5_10),
% 1.43/0.58    inference(unit_resulting_resolution,[],[f79,f279,f76])).
% 1.43/0.58  fof(f76,plain,(
% 1.43/0.58    ( ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f44])).
% 1.43/0.58  fof(f44,plain,(
% 1.43/0.58    ! [X0,X1] : (m1_subset_1(X0,X1) | ~r2_hidden(X0,X1))),
% 1.43/0.58    inference(ennf_transformation,[],[f5])).
% 1.43/0.58  fof(f5,axiom,(
% 1.43/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(X0,X1))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_subset)).
% 1.43/0.58  fof(f279,plain,(
% 1.43/0.58    ~m1_subset_1(sK4(sK1),sK1) | spl5_10),
% 1.43/0.58    inference(forward_demodulation,[],[f272,f112])).
% 1.43/0.58  fof(f112,plain,(
% 1.43/0.58    sK1 = u1_struct_0(sK3(sK0,sK1))),
% 1.43/0.58    inference(unit_resulting_resolution,[],[f49,f52,f47,f48,f72])).
% 1.43/0.58  fof(f72,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK3(X0,X1)) = X1) )),
% 1.43/0.58    inference(cnf_transformation,[],[f43])).
% 1.43/0.58  fof(f43,plain,(
% 1.43/0.58    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.43/0.58    inference(flattening,[],[f42])).
% 1.43/0.58  fof(f42,plain,(
% 1.43/0.58    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.43/0.58    inference(ennf_transformation,[],[f14])).
% 1.43/0.58  fof(f14,axiom,(
% 1.43/0.58    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).
% 1.43/0.58  fof(f272,plain,(
% 1.43/0.58    ~m1_subset_1(sK4(sK1),u1_struct_0(sK3(sK0,sK1))) | spl5_10),
% 1.43/0.58    inference(unit_resulting_resolution,[],[f52,f49,f109,f111,f270,f61])).
% 1.43/0.58  fof(f61,plain,(
% 1.43/0.58    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,u1_struct_0(X1)) | m1_subset_1(X2,u1_struct_0(X0))) )),
% 1.43/0.58    inference(cnf_transformation,[],[f31])).
% 1.43/0.58  fof(f31,plain,(
% 1.43/0.58    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.43/0.58    inference(flattening,[],[f30])).
% 1.43/0.58  fof(f30,plain,(
% 1.43/0.58    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.43/0.58    inference(ennf_transformation,[],[f10])).
% 1.43/0.58  fof(f10,axiom,(
% 1.43/0.58    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).
% 1.43/0.58  fof(f270,plain,(
% 1.43/0.58    ~m1_subset_1(sK4(sK1),u1_struct_0(sK0)) | spl5_10),
% 1.43/0.58    inference(avatar_component_clause,[],[f268])).
% 1.43/0.58  fof(f268,plain,(
% 1.43/0.58    spl5_10 <=> m1_subset_1(sK4(sK1),u1_struct_0(sK0))),
% 1.43/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_10])])).
% 1.43/0.58  fof(f111,plain,(
% 1.43/0.58    m1_pre_topc(sK3(sK0,sK1),sK0)),
% 1.43/0.58    inference(unit_resulting_resolution,[],[f49,f52,f47,f48,f71])).
% 1.43/0.58  fof(f71,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | v2_struct_0(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(sK3(X0,X1),X0)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f43])).
% 1.43/0.58  fof(f109,plain,(
% 1.43/0.58    ~v2_struct_0(sK3(sK0,sK1))),
% 1.43/0.58    inference(unit_resulting_resolution,[],[f49,f52,f47,f48,f69])).
% 1.43/0.58  fof(f69,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~v2_struct_0(sK3(X0,X1)) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f43])).
% 1.43/0.58  fof(f79,plain,(
% 1.43/0.58    r2_hidden(sK4(sK1),sK1)),
% 1.43/0.58    inference(unit_resulting_resolution,[],[f47,f77])).
% 1.43/0.58  fof(f77,plain,(
% 1.43/0.58    ( ! [X0] : (r2_hidden(sK4(X0),X0) | v1_xboole_0(X0)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f1])).
% 1.43/0.58  fof(f1,axiom,(
% 1.43/0.58    ! [X0] : (v1_xboole_0(X0) <=> ! [X1] : ~r2_hidden(X1,X0))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).
% 1.43/0.58  fof(f271,plain,(
% 1.43/0.58    ~spl5_10 | spl5_1 | ~spl5_2 | ~spl5_3),
% 1.43/0.58    inference(avatar_split_clause,[],[f266,f173,f103,f99,f268])).
% 1.43/0.58  fof(f173,plain,(
% 1.43/0.58    spl5_3 <=> ! [X1] : (~m1_subset_1(X1,u1_struct_0(sK0)) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0))),
% 1.43/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 1.43/0.58  fof(f266,plain,(
% 1.43/0.58    v2_tex_2(sK1,sK0) | ~m1_subset_1(sK4(sK1),u1_struct_0(sK0)) | (~spl5_2 | ~spl5_3)),
% 1.43/0.58    inference(superposition,[],[f264,f143])).
% 1.43/0.58  fof(f143,plain,(
% 1.43/0.58    sK1 = k1_tarski(sK4(sK1)) | ~spl5_2),
% 1.43/0.58    inference(unit_resulting_resolution,[],[f47,f105,f75,f139,f54])).
% 1.43/0.58  fof(f54,plain,(
% 1.43/0.58    ( ! [X0,X1] : (v1_xboole_0(X0) | v1_xboole_0(X1) | ~v1_zfmisc_1(X1) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 1.43/0.58    inference(cnf_transformation,[],[f25])).
% 1.43/0.58  fof(f25,plain,(
% 1.43/0.58    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 1.43/0.58    inference(flattening,[],[f24])).
% 1.43/0.58  fof(f24,plain,(
% 1.43/0.58    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 1.43/0.58    inference(ennf_transformation,[],[f15])).
% 1.43/0.58  fof(f15,axiom,(
% 1.43/0.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 1.43/0.58  fof(f139,plain,(
% 1.43/0.58    r1_tarski(k1_tarski(sK4(sK1)),sK1)),
% 1.43/0.58    inference(unit_resulting_resolution,[],[f96,f74])).
% 1.43/0.58  fof(f74,plain,(
% 1.43/0.58    ( ! [X0,X1] : (r1_tarski(X0,X1) | ~m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 1.43/0.58    inference(cnf_transformation,[],[f6])).
% 1.43/0.58  fof(f6,axiom,(
% 1.43/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 1.43/0.58  fof(f96,plain,(
% 1.43/0.58    m1_subset_1(k1_tarski(sK4(sK1)),k1_zfmisc_1(sK1))),
% 1.43/0.58    inference(unit_resulting_resolution,[],[f79,f63])).
% 1.43/0.58  fof(f63,plain,(
% 1.43/0.58    ( ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f33])).
% 1.43/0.58  fof(f33,plain,(
% 1.43/0.58    ! [X0,X1] : (m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)) | ~r2_hidden(X0,X1))),
% 1.43/0.58    inference(ennf_transformation,[],[f3])).
% 1.43/0.58  fof(f3,axiom,(
% 1.43/0.58    ! [X0,X1] : (r2_hidden(X0,X1) => m1_subset_1(k1_tarski(X0),k1_zfmisc_1(X1)))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_subset_1)).
% 1.43/0.58  fof(f75,plain,(
% 1.43/0.58    ( ! [X0] : (~v1_xboole_0(k1_tarski(X0))) )),
% 1.43/0.58    inference(cnf_transformation,[],[f2])).
% 1.43/0.58  fof(f2,axiom,(
% 1.43/0.58    ! [X0] : ~v1_xboole_0(k1_tarski(X0))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_xboole_0)).
% 1.43/0.58  fof(f105,plain,(
% 1.43/0.58    v1_zfmisc_1(sK1) | ~spl5_2),
% 1.43/0.58    inference(avatar_component_clause,[],[f103])).
% 1.43/0.58  fof(f264,plain,(
% 1.43/0.58    ( ! [X0] : (v2_tex_2(k1_tarski(X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl5_3),
% 1.43/0.58    inference(duplicate_literal_removal,[],[f263])).
% 1.43/0.58  fof(f263,plain,(
% 1.43/0.58    ( ! [X0] : (v2_tex_2(k1_tarski(X0),sK0) | ~m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,u1_struct_0(sK0))) ) | ~spl5_3),
% 1.43/0.58    inference(superposition,[],[f174,f116])).
% 1.43/0.58  fof(f116,plain,(
% 1.43/0.58    ( ! [X0] : (k1_tarski(X0) = k6_domain_1(u1_struct_0(sK0),X0) | ~m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.43/0.58    inference(resolution,[],[f114,f68])).
% 1.43/0.58  fof(f68,plain,(
% 1.43/0.58    ( ! [X0,X1] : (v1_xboole_0(X0) | ~m1_subset_1(X1,X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f41])).
% 1.43/0.58  fof(f41,plain,(
% 1.43/0.58    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.43/0.58    inference(flattening,[],[f40])).
% 1.43/0.58  fof(f40,plain,(
% 1.43/0.58    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.43/0.58    inference(ennf_transformation,[],[f11])).
% 1.43/0.58  fof(f11,axiom,(
% 1.43/0.58    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.43/0.58  fof(f114,plain,(
% 1.43/0.58    ~v1_xboole_0(u1_struct_0(sK0))),
% 1.43/0.58    inference(unit_resulting_resolution,[],[f47,f48,f62])).
% 1.43/0.58  fof(f62,plain,(
% 1.43/0.58    ( ! [X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f32])).
% 1.43/0.58  fof(f32,plain,(
% 1.43/0.58    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.43/0.58    inference(ennf_transformation,[],[f4])).
% 1.43/0.58  fof(f4,axiom,(
% 1.43/0.58    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.43/0.58  fof(f174,plain,(
% 1.43/0.58    ( ! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0) | ~m1_subset_1(X1,u1_struct_0(sK0))) ) | ~spl5_3),
% 1.43/0.58    inference(avatar_component_clause,[],[f173])).
% 1.43/0.58  fof(f213,plain,(
% 1.43/0.58    ~spl5_5),
% 1.43/0.58    inference(avatar_contradiction_clause,[],[f210])).
% 1.43/0.58  fof(f210,plain,(
% 1.43/0.58    $false | ~spl5_5),
% 1.43/0.58    inference(unit_resulting_resolution,[],[f49,f182])).
% 1.43/0.58  fof(f182,plain,(
% 1.43/0.58    v2_struct_0(sK0) | ~spl5_5),
% 1.43/0.58    inference(avatar_component_clause,[],[f180])).
% 1.43/0.58  fof(f180,plain,(
% 1.43/0.58    spl5_5 <=> v2_struct_0(sK0)),
% 1.43/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 1.43/0.58  fof(f190,plain,(
% 1.43/0.58    spl5_4),
% 1.43/0.58    inference(avatar_contradiction_clause,[],[f184])).
% 1.43/0.58  fof(f184,plain,(
% 1.43/0.58    $false | spl5_4),
% 1.43/0.58    inference(unit_resulting_resolution,[],[f52,f178])).
% 1.43/0.58  fof(f178,plain,(
% 1.43/0.58    ~l1_pre_topc(sK0) | spl5_4),
% 1.43/0.58    inference(avatar_component_clause,[],[f176])).
% 1.43/0.58  fof(f176,plain,(
% 1.43/0.58    spl5_4 <=> l1_pre_topc(sK0)),
% 1.43/0.58    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 1.43/0.58  fof(f183,plain,(
% 1.43/0.58    spl5_3 | ~spl5_4 | spl5_5),
% 1.43/0.58    inference(avatar_split_clause,[],[f84,f180,f176,f173])).
% 1.43/0.58  fof(f84,plain,(
% 1.43/0.58    ( ! [X1] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,u1_struct_0(sK0)) | v2_tex_2(k6_domain_1(u1_struct_0(sK0),X1),sK0)) )),
% 1.43/0.58    inference(resolution,[],[f50,f60])).
% 1.43/0.58  fof(f60,plain,(
% 1.43/0.58    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)) )),
% 1.43/0.58    inference(cnf_transformation,[],[f29])).
% 1.43/0.58  fof(f29,plain,(
% 1.43/0.58    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.43/0.58    inference(flattening,[],[f28])).
% 1.43/0.58  fof(f28,plain,(
% 1.43/0.58    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.43/0.58    inference(ennf_transformation,[],[f17])).
% 1.43/0.58  fof(f17,axiom,(
% 1.43/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 1.43/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).
% 1.43/0.58  fof(f108,plain,(
% 1.43/0.58    ~spl5_1 | ~spl5_2),
% 1.43/0.58    inference(avatar_split_clause,[],[f46,f103,f99])).
% 1.43/0.58  fof(f46,plain,(
% 1.43/0.58    ~v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 1.43/0.58    inference(cnf_transformation,[],[f21])).
% 1.43/0.58  fof(f106,plain,(
% 1.43/0.58    spl5_1 | spl5_2),
% 1.43/0.58    inference(avatar_split_clause,[],[f45,f103,f99])).
% 1.43/0.58  fof(f45,plain,(
% 1.43/0.58    v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 1.43/0.58    inference(cnf_transformation,[],[f21])).
% 1.43/0.58  % SZS output end Proof for theBenchmark
% 1.43/0.58  % (30235)------------------------------
% 1.43/0.58  % (30235)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.43/0.58  % (30235)Termination reason: Refutation
% 1.43/0.58  
% 1.43/0.58  % (30235)Memory used [KB]: 6396
% 1.43/0.58  % (30235)Time elapsed: 0.128 s
% 1.43/0.58  % (30235)------------------------------
% 1.43/0.58  % (30235)------------------------------
% 1.43/0.58  % (30230)Success in time 0.216 s
%------------------------------------------------------------------------------
