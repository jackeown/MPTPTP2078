%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:36 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :  105 ( 898 expanded)
%              Number of leaves         :   10 ( 153 expanded)
%              Depth                    :   21
%              Number of atoms          :  423 (5285 expanded)
%              Number of equality atoms :   14 ( 130 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f144,plain,(
    $false ),
    inference(subsumption_resolution,[],[f143,f136])).

fof(f136,plain,(
    ~ v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f32,f131])).

fof(f131,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f124,f129])).

fof(f129,plain,(
    v1_tdlat_3(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f86,f128])).

fof(f128,plain,(
    v7_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f127,f110])).

fof(f110,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v7_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f89,f109])).

fof(f109,plain,(
    l1_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f88,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f88,plain,(
    l1_pre_topc(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f72,f38])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).

fof(f72,plain,
    ( ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK2(sK0,sK1)) ),
    inference(resolution,[],[f63,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( l1_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => l1_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f63,plain,(
    m1_pre_topc(sK2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f62,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f62,plain,
    ( v2_struct_0(sK0)
    | m1_pre_topc(sK2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f61,f33])).

fof(f33,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f61,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f60,f38])).

fof(f60,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK2(sK0,sK1),sK0) ),
    inference(resolution,[],[f46,f34])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | m1_pre_topc(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
            & ~ v1_xboole_0(X1) )
         => ? [X2] :
              ( u1_struct_0(X2) = X1
              & m1_pre_topc(X2,X0)
              & ~ v2_struct_0(X2) ) ) ) ),
    inference(pure_predicate_removal,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).

fof(f89,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ l1_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1)) ),
    inference(superposition,[],[f41,f67])).

fof(f67,plain,(
    sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f66,f35])).

fof(f66,plain,
    ( v2_struct_0(sK0)
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f65,f33])).

fof(f65,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f64,f38])).

fof(f64,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f47,f34])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | u1_struct_0(sK2(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v7_struct_0(X0) )
     => ~ v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).

fof(f127,plain,
    ( v1_zfmisc_1(sK1)
    | v7_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f125,f77])).

fof(f77,plain,
    ( ~ v1_tdlat_3(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f76,f59])).

fof(f59,plain,(
    ~ v2_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f58,f35])).

fof(f58,plain,
    ( v2_struct_0(sK0)
    | ~ v2_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f57,f33])).

fof(f57,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f56,f38])).

fof(f56,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(sK2(sK0,sK1)) ),
    inference(resolution,[],[f45,f34])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_struct_0(sK2(X0,X1)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f76,plain,
    ( v2_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ v1_tdlat_3(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f75,f35])).

fof(f75,plain,
    ( v2_struct_0(sK0)
    | v2_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ v1_tdlat_3(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f74,f38])).

fof(f74,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ v1_tdlat_3(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f73,f37])).

fof(f37,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f73,plain,
    ( ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ v1_tdlat_3(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f68,f36])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f68,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2(sK0,sK1))
    | v7_struct_0(sK2(sK0,sK1))
    | ~ v1_tdlat_3(sK2(sK0,sK1)) ),
    inference(resolution,[],[f63,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | v7_struct_0(X1)
      | ~ v1_tdlat_3(X1) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).

fof(f125,plain,
    ( v1_tdlat_3(sK2(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f119,f31])).

fof(f31,plain,
    ( v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f119,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f118,f35])).

fof(f118,plain,
    ( v2_struct_0(sK0)
    | v1_tdlat_3(sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f117,f63])).

fof(f117,plain,
    ( ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | v2_struct_0(sK0)
    | v1_tdlat_3(sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f115,f38])).

fof(f115,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | v2_struct_0(sK0)
    | v1_tdlat_3(sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f105,f34])).

fof(f105,plain,(
    ! [X4] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_pre_topc(X4)
      | ~ m1_pre_topc(sK2(sK0,sK1),X4)
      | v2_struct_0(X4)
      | v1_tdlat_3(sK2(sK0,sK1))
      | ~ v2_tex_2(sK1,X4) ) ),
    inference(subsumption_resolution,[],[f94,f59])).

fof(f94,plain,(
    ! [X4] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ l1_pre_topc(X4)
      | v2_struct_0(sK2(sK0,sK1))
      | ~ m1_pre_topc(sK2(sK0,sK1),X4)
      | v2_struct_0(X4)
      | v1_tdlat_3(sK2(sK0,sK1))
      | ~ v2_tex_2(sK1,X4) ) ),
    inference(superposition,[],[f52,f67])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | v1_tdlat_3(X1)
      | ~ v2_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v1_tdlat_3(X1)
      | ~ v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v2_tex_2(X2,X0)
              <=> v1_tdlat_3(X1) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
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
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( v2_tex_2(X2,X0)
                <=> v1_tdlat_3(X1) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).

fof(f86,plain,
    ( ~ v7_struct_0(sK2(sK0,sK1))
    | v1_tdlat_3(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f83,f85])).

fof(f85,plain,(
    v2_pre_topc(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f84,f36])).

fof(f84,plain,
    ( ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f71,f38])).

fof(f71,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v2_pre_topc(sK2(sK0,sK1)) ),
    inference(resolution,[],[f63,f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_pre_topc(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_pre_topc(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).

fof(f83,plain,
    ( ~ v7_struct_0(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK2(sK0,sK1))
    | v1_tdlat_3(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f82,f59])).

fof(f82,plain,
    ( v2_struct_0(sK2(sK0,sK1))
    | ~ v7_struct_0(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK2(sK0,sK1))
    | v1_tdlat_3(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f81,f35])).

fof(f81,plain,
    ( v2_struct_0(sK0)
    | v2_struct_0(sK2(sK0,sK1))
    | ~ v7_struct_0(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK2(sK0,sK1))
    | v1_tdlat_3(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f70,f38])).

fof(f70,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK2(sK0,sK1))
    | ~ v7_struct_0(sK2(sK0,sK1))
    | ~ v2_pre_topc(sK2(sK0,sK1))
    | v1_tdlat_3(sK2(sK0,sK1)) ),
    inference(resolution,[],[f63,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v7_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | v1_tdlat_3(X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tdlat_3(X1)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_pre_topc(X1)
          | ~ v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tdlat_3(X1)
            & v1_tdlat_3(X1)
            & ~ v2_struct_0(X1) )
          | ~ v2_pre_topc(X1)
          | ~ v7_struct_0(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( v2_pre_topc(X1)
              & v7_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ( v2_tdlat_3(X1)
              & v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc25_tex_2)).

fof(f124,plain,
    ( ~ v1_tdlat_3(sK2(sK0,sK1))
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f123,f35])).

fof(f123,plain,
    ( v2_struct_0(sK0)
    | ~ v1_tdlat_3(sK2(sK0,sK1))
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f122,f63])).

fof(f122,plain,
    ( ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | v2_struct_0(sK0)
    | ~ v1_tdlat_3(sK2(sK0,sK1))
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f120,f38])).

fof(f120,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_pre_topc(sK2(sK0,sK1),sK0)
    | v2_struct_0(sK0)
    | ~ v1_tdlat_3(sK2(sK0,sK1))
    | v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f108,f34])).

fof(f108,plain,(
    ! [X6] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ l1_pre_topc(X6)
      | ~ m1_pre_topc(sK2(sK0,sK1),X6)
      | v2_struct_0(X6)
      | ~ v1_tdlat_3(sK2(sK0,sK1))
      | v2_tex_2(sK1,X6) ) ),
    inference(subsumption_resolution,[],[f96,f59])).

fof(f96,plain,(
    ! [X6] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X6)))
      | ~ l1_pre_topc(X6)
      | v2_struct_0(sK2(sK0,sK1))
      | ~ m1_pre_topc(sK2(sK0,sK1),X6)
      | v2_struct_0(X6)
      | ~ v1_tdlat_3(sK2(sK0,sK1))
      | v2_tex_2(sK1,X6) ) ),
    inference(superposition,[],[f53,f67])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(u1_struct_0(X1),X0) ) ),
    inference(equality_resolution,[],[f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | ~ v1_tdlat_3(X1)
      | v2_tex_2(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f32,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f143,plain,(
    v1_zfmisc_1(sK1) ),
    inference(forward_demodulation,[],[f142,f67])).

fof(f142,plain,(
    v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f141,f109])).

fof(f141,plain,
    ( ~ l1_struct_0(sK2(sK0,sK1))
    | v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1))) ),
    inference(resolution,[],[f128,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v7_struct_0(X0)
      | ~ l1_struct_0(X0)
      | v1_zfmisc_1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 12:50:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.42  % (23958)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.42  % (23958)Refutation not found, incomplete strategy% (23958)------------------------------
% 0.22/0.42  % (23958)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.42  % (23958)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.42  
% 0.22/0.42  % (23958)Memory used [KB]: 6140
% 0.22/0.42  % (23958)Time elapsed: 0.004 s
% 0.22/0.42  % (23958)------------------------------
% 0.22/0.42  % (23958)------------------------------
% 0.22/0.45  % (23947)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.46  % (23947)Refutation not found, incomplete strategy% (23947)------------------------------
% 0.22/0.46  % (23947)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.46  % (23947)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.46  
% 0.22/0.46  % (23947)Memory used [KB]: 10618
% 0.22/0.46  % (23947)Time elapsed: 0.032 s
% 0.22/0.46  % (23947)------------------------------
% 0.22/0.46  % (23947)------------------------------
% 0.22/0.48  % (23966)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.48  % (23963)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.49  % (23966)Refutation not found, incomplete strategy% (23966)------------------------------
% 0.22/0.49  % (23966)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (23966)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.49  
% 0.22/0.49  % (23966)Memory used [KB]: 10618
% 0.22/0.49  % (23966)Time elapsed: 0.056 s
% 0.22/0.49  % (23966)------------------------------
% 0.22/0.49  % (23966)------------------------------
% 0.22/0.49  % (23963)Refutation found. Thanks to Tanya!
% 0.22/0.49  % SZS status Theorem for theBenchmark
% 0.22/0.49  % SZS output start Proof for theBenchmark
% 0.22/0.49  fof(f144,plain,(
% 0.22/0.49    $false),
% 0.22/0.49    inference(subsumption_resolution,[],[f143,f136])).
% 0.22/0.49  fof(f136,plain,(
% 0.22/0.49    ~v1_zfmisc_1(sK1)),
% 0.22/0.49    inference(subsumption_resolution,[],[f32,f131])).
% 0.22/0.49  fof(f131,plain,(
% 0.22/0.49    v2_tex_2(sK1,sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f124,f129])).
% 0.22/0.49  fof(f129,plain,(
% 0.22/0.49    v1_tdlat_3(sK2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f86,f128])).
% 0.22/0.49  fof(f128,plain,(
% 0.22/0.49    v7_struct_0(sK2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f127,f110])).
% 0.22/0.49  fof(f110,plain,(
% 0.22/0.49    ~v1_zfmisc_1(sK1) | v7_struct_0(sK2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f89,f109])).
% 0.22/0.49  fof(f109,plain,(
% 0.22/0.49    l1_struct_0(sK2(sK0,sK1))),
% 0.22/0.49    inference(resolution,[],[f88,f39])).
% 0.22/0.49  fof(f39,plain,(
% 0.22/0.49    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f15])).
% 0.22/0.49  fof(f15,plain,(
% 0.22/0.49    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f2])).
% 0.22/0.49  fof(f2,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.22/0.49  fof(f88,plain,(
% 0.22/0.49    l1_pre_topc(sK2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f72,f38])).
% 0.22/0.49  fof(f38,plain,(
% 0.22/0.49    l1_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f14,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f13])).
% 0.22/0.49  fof(f13,plain,(
% 0.22/0.49    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f11])).
% 0.22/0.49  fof(f11,negated_conjecture,(
% 0.22/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.22/0.49    inference(negated_conjecture,[],[f10])).
% 0.22/0.49  fof(f10,conjecture,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.22/0.49  fof(f72,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | l1_pre_topc(sK2(sK0,sK1))),
% 0.22/0.49    inference(resolution,[],[f63,f40])).
% 0.22/0.49  fof(f40,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f16])).
% 0.22/0.49  fof(f16,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.49    inference(ennf_transformation,[],[f3])).
% 0.22/0.49  fof(f3,axiom,(
% 0.22/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.22/0.49  fof(f63,plain,(
% 0.22/0.49    m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f62,f35])).
% 0.22/0.49  fof(f35,plain,(
% 0.22/0.49    ~v2_struct_0(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f62,plain,(
% 0.22/0.49    v2_struct_0(sK0) | m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f61,f33])).
% 0.22/0.49  fof(f33,plain,(
% 0.22/0.49    ~v1_xboole_0(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f61,plain,(
% 0.22/0.49    v1_xboole_0(sK1) | v2_struct_0(sK0) | m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f60,f38])).
% 0.22/0.49  fof(f60,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.22/0.49    inference(resolution,[],[f46,f34])).
% 0.22/0.49  fof(f34,plain,(
% 0.22/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f46,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | m1_pre_topc(sK2(X0,X1),X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f24,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f23])).
% 0.22/0.49  fof(f23,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f12])).
% 0.22/0.49  fof(f12,plain,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & ~v2_struct_0(X2))))),
% 0.22/0.49    inference(pure_predicate_removal,[],[f8])).
% 0.22/0.49  fof(f8,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_tsep_1)).
% 0.22/0.49  fof(f89,plain,(
% 0.22/0.49    ~v1_zfmisc_1(sK1) | ~l1_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1))),
% 0.22/0.49    inference(superposition,[],[f41,f67])).
% 0.22/0.49  fof(f67,plain,(
% 0.22/0.49    sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f66,f35])).
% 0.22/0.49  fof(f66,plain,(
% 0.22/0.49    v2_struct_0(sK0) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f65,f33])).
% 0.22/0.49  fof(f65,plain,(
% 0.22/0.49    v1_xboole_0(sK1) | v2_struct_0(sK0) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f64,f38])).
% 0.22/0.49  fof(f64,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.22/0.49    inference(resolution,[],[f47,f34])).
% 0.22/0.49  fof(f47,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | u1_struct_0(sK2(X0,X1)) = X1) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f41,plain,(
% 0.22/0.49    ( ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f18])).
% 0.22/0.49  fof(f18,plain,(
% 0.22/0.49    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | v7_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f17])).
% 0.22/0.49  fof(f17,plain,(
% 0.22/0.49    ! [X0] : (~v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | v7_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f4])).
% 0.22/0.49  fof(f4,axiom,(
% 0.22/0.49    ! [X0] : ((l1_struct_0(X0) & ~v7_struct_0(X0)) => ~v1_zfmisc_1(u1_struct_0(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_struct_0)).
% 0.22/0.49  fof(f127,plain,(
% 0.22/0.49    v1_zfmisc_1(sK1) | v7_struct_0(sK2(sK0,sK1))),
% 0.22/0.49    inference(resolution,[],[f125,f77])).
% 0.22/0.49  fof(f77,plain,(
% 0.22/0.49    ~v1_tdlat_3(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f76,f59])).
% 0.22/0.49  fof(f59,plain,(
% 0.22/0.49    ~v2_struct_0(sK2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f58,f35])).
% 0.22/0.49  fof(f58,plain,(
% 0.22/0.49    v2_struct_0(sK0) | ~v2_struct_0(sK2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f57,f33])).
% 0.22/0.49  fof(f57,plain,(
% 0.22/0.49    v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_struct_0(sK2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f56,f38])).
% 0.22/0.49  fof(f56,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_struct_0(sK2(sK0,sK1))),
% 0.22/0.49    inference(resolution,[],[f45,f34])).
% 0.22/0.49  fof(f45,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_struct_0(sK2(X0,X1))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f24])).
% 0.22/0.49  fof(f76,plain,(
% 0.22/0.49    v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | ~v1_tdlat_3(sK2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f75,f35])).
% 0.22/0.49  fof(f75,plain,(
% 0.22/0.49    v2_struct_0(sK0) | v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | ~v1_tdlat_3(sK2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f74,f38])).
% 0.22/0.49  fof(f74,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | ~v1_tdlat_3(sK2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f73,f37])).
% 0.22/0.49  fof(f37,plain,(
% 0.22/0.49    v2_tdlat_3(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f73,plain,(
% 0.22/0.49    ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | ~v1_tdlat_3(sK2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f68,f36])).
% 0.22/0.49  fof(f36,plain,(
% 0.22/0.49    v2_pre_topc(sK0)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f68,plain,(
% 0.22/0.49    ~v2_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(sK2(sK0,sK1)) | v7_struct_0(sK2(sK0,sK1)) | ~v1_tdlat_3(sK2(sK0,sK1))),
% 0.22/0.49    inference(resolution,[],[f63,f42])).
% 0.22/0.49  fof(f42,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | v7_struct_0(X1) | ~v1_tdlat_3(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f20])).
% 0.22/0.49  fof(f20,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f19])).
% 0.22/0.49  fof(f19,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((~v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f7])).
% 0.22/0.49  fof(f7,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((~v7_struct_0(X1) & ~v2_struct_0(X1)) => (~v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc32_tex_2)).
% 0.22/0.49  fof(f125,plain,(
% 0.22/0.49    v1_tdlat_3(sK2(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 0.22/0.49    inference(resolution,[],[f119,f31])).
% 0.22/0.49  fof(f31,plain,(
% 0.22/0.49    v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f119,plain,(
% 0.22/0.49    ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f118,f35])).
% 0.22/0.49  fof(f118,plain,(
% 0.22/0.49    v2_struct_0(sK0) | v1_tdlat_3(sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f117,f63])).
% 0.22/0.49  fof(f117,plain,(
% 0.22/0.49    ~m1_pre_topc(sK2(sK0,sK1),sK0) | v2_struct_0(sK0) | v1_tdlat_3(sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f115,f38])).
% 0.22/0.49  fof(f115,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2(sK0,sK1),sK0) | v2_struct_0(sK0) | v1_tdlat_3(sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 0.22/0.49    inference(resolution,[],[f105,f34])).
% 0.22/0.49  fof(f105,plain,(
% 0.22/0.49    ( ! [X4] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_pre_topc(X4) | ~m1_pre_topc(sK2(sK0,sK1),X4) | v2_struct_0(X4) | v1_tdlat_3(sK2(sK0,sK1)) | ~v2_tex_2(sK1,X4)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f94,f59])).
% 0.22/0.49  fof(f94,plain,(
% 0.22/0.49    ( ! [X4] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X4))) | ~l1_pre_topc(X4) | v2_struct_0(sK2(sK0,sK1)) | ~m1_pre_topc(sK2(sK0,sK1),X4) | v2_struct_0(X4) | v1_tdlat_3(sK2(sK0,sK1)) | ~v2_tex_2(sK1,X4)) )),
% 0.22/0.49    inference(superposition,[],[f52,f67])).
% 0.22/0.49  fof(f52,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | v1_tdlat_3(X1) | ~v2_tex_2(u1_struct_0(X1),X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f49])).
% 0.22/0.49  fof(f49,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v1_tdlat_3(X1) | ~v2_tex_2(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f26,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : ((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f25])).
% 0.22/0.49  fof(f25,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (! [X2] : (((v2_tex_2(X2,X0) <=> v1_tdlat_3(X1)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f9])).
% 0.22/0.49  fof(f9,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => (v2_tex_2(X2,X0) <=> v1_tdlat_3(X1))))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t26_tex_2)).
% 0.22/0.49  fof(f86,plain,(
% 0.22/0.49    ~v7_struct_0(sK2(sK0,sK1)) | v1_tdlat_3(sK2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f83,f85])).
% 0.22/0.49  fof(f85,plain,(
% 0.22/0.49    v2_pre_topc(sK2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f84,f36])).
% 0.22/0.49  fof(f84,plain,(
% 0.22/0.49    ~v2_pre_topc(sK0) | v2_pre_topc(sK2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f71,f38])).
% 0.22/0.49  fof(f71,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v2_pre_topc(sK2(sK0,sK1))),
% 0.22/0.49    inference(resolution,[],[f63,f51])).
% 0.22/0.49  fof(f51,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_pre_topc(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f30])).
% 0.22/0.49  fof(f30,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.22/0.49    inference(flattening,[],[f29])).
% 0.22/0.49  fof(f29,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (v2_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f1])).
% 0.22/0.49  fof(f1,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_pre_topc(X1)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_pre_topc)).
% 0.22/0.49  fof(f83,plain,(
% 0.22/0.49    ~v7_struct_0(sK2(sK0,sK1)) | ~v2_pre_topc(sK2(sK0,sK1)) | v1_tdlat_3(sK2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f82,f59])).
% 0.22/0.49  fof(f82,plain,(
% 0.22/0.49    v2_struct_0(sK2(sK0,sK1)) | ~v7_struct_0(sK2(sK0,sK1)) | ~v2_pre_topc(sK2(sK0,sK1)) | v1_tdlat_3(sK2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f81,f35])).
% 0.22/0.49  fof(f81,plain,(
% 0.22/0.49    v2_struct_0(sK0) | v2_struct_0(sK2(sK0,sK1)) | ~v7_struct_0(sK2(sK0,sK1)) | ~v2_pre_topc(sK2(sK0,sK1)) | v1_tdlat_3(sK2(sK0,sK1))),
% 0.22/0.49    inference(subsumption_resolution,[],[f70,f38])).
% 0.22/0.49  fof(f70,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(sK2(sK0,sK1)) | ~v7_struct_0(sK2(sK0,sK1)) | ~v2_pre_topc(sK2(sK0,sK1)) | v1_tdlat_3(sK2(sK0,sK1))),
% 0.22/0.49    inference(resolution,[],[f63,f43])).
% 0.22/0.49  fof(f43,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~v7_struct_0(X1) | ~v2_pre_topc(X1) | v1_tdlat_3(X1)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f22])).
% 0.22/0.49  fof(f22,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : ((v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) | ~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f21])).
% 0.22/0.49  fof(f21,plain,(
% 0.22/0.49    ! [X0] : (! [X1] : (((v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)) | (~v2_pre_topc(X1) | ~v7_struct_0(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f6])).
% 0.22/0.49  fof(f6,axiom,(
% 0.22/0.49    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((v2_pre_topc(X1) & v7_struct_0(X1) & ~v2_struct_0(X1)) => (v2_tdlat_3(X1) & v1_tdlat_3(X1) & ~v2_struct_0(X1)))))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc25_tex_2)).
% 0.22/0.49  fof(f124,plain,(
% 0.22/0.49    ~v1_tdlat_3(sK2(sK0,sK1)) | v2_tex_2(sK1,sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f123,f35])).
% 0.22/0.49  fof(f123,plain,(
% 0.22/0.49    v2_struct_0(sK0) | ~v1_tdlat_3(sK2(sK0,sK1)) | v2_tex_2(sK1,sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f122,f63])).
% 0.22/0.49  fof(f122,plain,(
% 0.22/0.49    ~m1_pre_topc(sK2(sK0,sK1),sK0) | v2_struct_0(sK0) | ~v1_tdlat_3(sK2(sK0,sK1)) | v2_tex_2(sK1,sK0)),
% 0.22/0.49    inference(subsumption_resolution,[],[f120,f38])).
% 0.22/0.49  fof(f120,plain,(
% 0.22/0.49    ~l1_pre_topc(sK0) | ~m1_pre_topc(sK2(sK0,sK1),sK0) | v2_struct_0(sK0) | ~v1_tdlat_3(sK2(sK0,sK1)) | v2_tex_2(sK1,sK0)),
% 0.22/0.49    inference(resolution,[],[f108,f34])).
% 0.22/0.49  fof(f108,plain,(
% 0.22/0.49    ( ! [X6] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X6))) | ~l1_pre_topc(X6) | ~m1_pre_topc(sK2(sK0,sK1),X6) | v2_struct_0(X6) | ~v1_tdlat_3(sK2(sK0,sK1)) | v2_tex_2(sK1,X6)) )),
% 0.22/0.49    inference(subsumption_resolution,[],[f96,f59])).
% 0.22/0.49  fof(f96,plain,(
% 0.22/0.49    ( ! [X6] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X6))) | ~l1_pre_topc(X6) | v2_struct_0(sK2(sK0,sK1)) | ~m1_pre_topc(sK2(sK0,sK1),X6) | v2_struct_0(X6) | ~v1_tdlat_3(sK2(sK0,sK1)) | v2_tex_2(sK1,X6)) )),
% 0.22/0.49    inference(superposition,[],[f53,f67])).
% 0.22/0.49  fof(f53,plain,(
% 0.22/0.49    ( ! [X0,X1] : (~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~v1_tdlat_3(X1) | v2_tex_2(u1_struct_0(X1),X0)) )),
% 0.22/0.49    inference(equality_resolution,[],[f48])).
% 0.22/0.49  fof(f48,plain,(
% 0.22/0.49    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | ~v1_tdlat_3(X1) | v2_tex_2(X2,X0)) )),
% 0.22/0.49    inference(cnf_transformation,[],[f26])).
% 0.22/0.49  fof(f32,plain,(
% 0.22/0.49    ~v2_tex_2(sK1,sK0) | ~v1_zfmisc_1(sK1)),
% 0.22/0.49    inference(cnf_transformation,[],[f14])).
% 0.22/0.49  fof(f143,plain,(
% 0.22/0.49    v1_zfmisc_1(sK1)),
% 0.22/0.49    inference(forward_demodulation,[],[f142,f67])).
% 0.22/0.49  fof(f142,plain,(
% 0.22/0.49    v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1)))),
% 0.22/0.49    inference(subsumption_resolution,[],[f141,f109])).
% 0.22/0.49  fof(f141,plain,(
% 0.22/0.49    ~l1_struct_0(sK2(sK0,sK1)) | v1_zfmisc_1(u1_struct_0(sK2(sK0,sK1)))),
% 0.22/0.49    inference(resolution,[],[f128,f50])).
% 0.22/0.49  fof(f50,plain,(
% 0.22/0.49    ( ! [X0] : (~v7_struct_0(X0) | ~l1_struct_0(X0) | v1_zfmisc_1(u1_struct_0(X0))) )),
% 0.22/0.49    inference(cnf_transformation,[],[f28])).
% 0.22/0.49  fof(f28,plain,(
% 0.22/0.49    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.22/0.49    inference(flattening,[],[f27])).
% 0.22/0.49  fof(f27,plain,(
% 0.22/0.49    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.22/0.49    inference(ennf_transformation,[],[f5])).
% 0.22/0.49  fof(f5,axiom,(
% 0.22/0.49    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.22/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.22/0.49  % SZS output end Proof for theBenchmark
% 0.22/0.49  % (23963)------------------------------
% 0.22/0.49  % (23963)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.49  % (23963)Termination reason: Refutation
% 0.22/0.49  
% 0.22/0.49  % (23963)Memory used [KB]: 1663
% 0.22/0.49  % (23963)Time elapsed: 0.069 s
% 0.22/0.49  % (23963)------------------------------
% 0.22/0.49  % (23963)------------------------------
% 0.22/0.49  % (23945)Success in time 0.126 s
%------------------------------------------------------------------------------
