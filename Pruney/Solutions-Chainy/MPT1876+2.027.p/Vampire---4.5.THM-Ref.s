%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  142 (3916 expanded)
%              Number of leaves         :   12 ( 688 expanded)
%              Depth                    :   45
%              Number of atoms          :  507 (23477 expanded)
%              Number of equality atoms :   67 ( 789 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f235,plain,(
    $false ),
    inference(subsumption_resolution,[],[f234,f218])).

fof(f218,plain,(
    v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f217,f34])).

fof(f34,plain,
    ( v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f217,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f216,f130])).

fof(f130,plain,
    ( l1_struct_0(sK3(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f129,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f129,plain,
    ( l1_pre_topc(sK3(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f122,f41])).

fof(f41,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f122,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK3(sK0,sK1)) ),
    inference(resolution,[],[f120,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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

fof(f120,plain,
    ( m1_pre_topc(sK3(sK0,sK1),sK0)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f119,f38])).

fof(f38,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f119,plain,
    ( v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | m1_pre_topc(sK3(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f118,f36])).

fof(f36,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f118,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | m1_pre_topc(sK3(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f117,f41])).

fof(f117,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | m1_pre_topc(sK3(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f114,f39])).

fof(f39,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f114,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | m1_pre_topc(sK3(sK0,sK1),sK0) ),
    inference(resolution,[],[f53,f37])).

fof(f37,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | m1_pre_topc(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f25])).

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
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f216,plain,
    ( ~ l1_struct_0(sK3(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f215,f35])).

fof(f35,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f215,plain,
    ( ~ l1_struct_0(sK3(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f209,f128])).

fof(f128,plain,
    ( v7_struct_0(sK3(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f127,f102])).

fof(f102,plain,
    ( v1_tdlat_3(sK3(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f101,f38])).

fof(f101,plain,
    ( v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f100,f36])).

fof(f100,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f99,f41])).

fof(f99,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f97,f39])).

fof(f97,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK3(sK0,sK1)) ),
    inference(resolution,[],[f52,f37])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | v1_tdlat_3(sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f127,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v1_tdlat_3(sK3(sK0,sK1))
    | v7_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f126,f90])).

fof(f90,plain,
    ( ~ v2_struct_0(sK3(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f89,f38])).

fof(f89,plain,
    ( v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v2_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f88,f36])).

fof(f88,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v2_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f87,f41])).

fof(f87,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v2_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f85,f39])).

fof(f85,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v2_struct_0(sK3(sK0,sK1)) ),
    inference(resolution,[],[f50,f37])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v2_struct_0(sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f126,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK3(sK0,sK1))
    | ~ v1_tdlat_3(sK3(sK0,sK1))
    | v7_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f125,f38])).

fof(f125,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK3(sK0,sK1))
    | ~ v1_tdlat_3(sK3(sK0,sK1))
    | v7_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f124,f41])).

fof(f124,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK3(sK0,sK1))
    | ~ v1_tdlat_3(sK3(sK0,sK1))
    | v7_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f123,f40])).

fof(f40,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f123,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK3(sK0,sK1))
    | ~ v1_tdlat_3(sK3(sK0,sK1))
    | v7_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f121,f39])).

fof(f121,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_struct_0(sK3(sK0,sK1))
    | ~ v1_tdlat_3(sK3(sK0,sK1))
    | v7_struct_0(sK3(sK0,sK1)) ),
    inference(resolution,[],[f120,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_struct_0(X1)
      | ~ v1_tdlat_3(X1)
      | v7_struct_0(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
          | ~ v1_tdlat_3(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v7_struct_0(X1)
            & ~ v2_struct_0(X1) )
          | ~ v1_tdlat_3(X1)
          | v2_struct_0(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( ( v1_tdlat_3(X1)
              & ~ v2_struct_0(X1) )
           => ( v7_struct_0(X1)
              & ~ v2_struct_0(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc31_tex_2)).

fof(f209,plain,
    ( ~ v7_struct_0(sK3(sK0,sK1))
    | ~ l1_struct_0(sK3(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(superposition,[],[f55,f202])).

fof(f202,plain,(
    sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f201,f138])).

fof(f138,plain,
    ( v1_zfmisc_1(sK1)
    | sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(resolution,[],[f137,f34])).

fof(f137,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f136,f38])).

fof(f136,plain,
    ( v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f135,f36])).

fof(f135,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f134,f41])).

fof(f134,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f131,f39])).

fof(f131,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(resolution,[],[f54,f37])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | u1_struct_0(sK3(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f201,plain,
    ( sK1 = u1_struct_0(sK3(sK0,sK1))
    | ~ v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f200,f36])).

fof(f200,plain,
    ( sK1 = u1_struct_0(sK3(sK0,sK1))
    | v1_xboole_0(sK1)
    | ~ v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f199,f66])).

fof(f66,plain,(
    ! [X0] :
      ( r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f65])).

fof(f65,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | r2_hidden(sK2(X0),X0)
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(resolution,[],[f56,f42])).

fof(f42,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,X1)
      | v1_xboole_0(X1)
      | r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( r2_hidden(X0,X1)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,X1)
     => ( r2_hidden(X0,X1)
        | v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).

fof(f199,plain,
    ( ~ r2_hidden(sK2(sK1),sK1)
    | sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(resolution,[],[f197,f68])).

fof(f68,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ r2_hidden(X0,sK1) ) ),
    inference(resolution,[],[f58,f37])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f197,plain,
    ( ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f195,f137])).

fof(f195,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(backward_demodulation,[],[f166,f191])).

fof(f191,plain,(
    sK1 = k1_tarski(sK2(sK1)) ),
    inference(duplicate_literal_removal,[],[f183])).

fof(f183,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | sK1 = k1_tarski(sK2(sK1))
    | sK1 = k1_tarski(sK2(sK1)) ),
    inference(superposition,[],[f175,f176])).

fof(f176,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | sK1 = k1_tarski(sK2(sK1)) ),
    inference(subsumption_resolution,[],[f174,f36])).

fof(f174,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | sK1 = k6_domain_1(sK1,sK2(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f171,f43])).

fof(f43,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | k6_domain_1(X0,sK2(X0)) = X0
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f171,plain,
    ( v1_zfmisc_1(sK1)
    | sK1 = k1_tarski(sK2(sK1)) ),
    inference(resolution,[],[f170,f34])).

fof(f170,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | sK1 = k1_tarski(sK2(sK1)) ),
    inference(subsumption_resolution,[],[f169,f130])).

fof(f169,plain,
    ( ~ l1_struct_0(sK3(sK0,sK1))
    | sK1 = k1_tarski(sK2(sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f168,f35])).

fof(f168,plain,
    ( ~ l1_struct_0(sK3(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | sK1 = k1_tarski(sK2(sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f157,f128])).

fof(f157,plain,
    ( ~ v7_struct_0(sK3(sK0,sK1))
    | ~ l1_struct_0(sK3(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | sK1 = k1_tarski(sK2(sK1)) ),
    inference(superposition,[],[f55,f150])).

fof(f150,plain,
    ( sK1 = u1_struct_0(sK3(sK0,sK1))
    | sK1 = k1_tarski(sK2(sK1)) ),
    inference(duplicate_literal_removal,[],[f146])).

fof(f146,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | sK1 = u1_struct_0(sK3(sK0,sK1))
    | sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(superposition,[],[f142,f143])).

fof(f143,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f141,f36])).

fof(f141,plain,
    ( sK1 = u1_struct_0(sK3(sK0,sK1))
    | sK1 = k6_domain_1(sK1,sK2(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f138,f43])).

fof(f142,plain,
    ( k1_tarski(sK2(sK1)) = k6_domain_1(sK1,sK2(sK1))
    | sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f140,f36])).

fof(f140,plain,
    ( sK1 = u1_struct_0(sK3(sK0,sK1))
    | k1_tarski(sK2(sK1)) = k6_domain_1(sK1,sK2(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f138,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | k6_domain_1(X0,sK2(X0)) = k1_tarski(sK2(X0))
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f73])).

fof(f73,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k6_domain_1(X0,sK2(X0)) = k1_tarski(sK2(X0))
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(resolution,[],[f57,f42])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f175,plain,
    ( k1_tarski(sK2(sK1)) = k6_domain_1(sK1,sK2(sK1))
    | sK1 = k1_tarski(sK2(sK1)) ),
    inference(subsumption_resolution,[],[f173,f36])).

fof(f173,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | k1_tarski(sK2(sK1)) = k6_domain_1(sK1,sK2(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f171,f75])).

fof(f166,plain,
    ( v2_tex_2(k1_tarski(sK2(sK1)),sK0)
    | ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f165,f38])).

fof(f165,plain,
    ( v2_tex_2(k1_tarski(sK2(sK1)),sK0)
    | ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f164,f41])).

fof(f164,plain,
    ( v2_tex_2(k1_tarski(sK2(sK1)),sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f162,f39])).

fof(f162,plain,
    ( v2_tex_2(k1_tarski(sK2(sK1)),sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(superposition,[],[f49,f139])).

fof(f139,plain,
    ( k1_tarski(sK2(sK1)) = k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(resolution,[],[f138,f78])).

fof(f78,plain,
    ( ~ v1_zfmisc_1(sK1)
    | k1_tarski(sK2(sK1)) = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) ),
    inference(subsumption_resolution,[],[f77,f36])).

fof(f77,plain,
    ( k1_tarski(sK2(sK1)) = k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | v1_xboole_0(sK1)
    | ~ v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f76,f66])).

fof(f76,plain,(
    ! [X1] :
      ( ~ r2_hidden(X1,sK1)
      | k1_tarski(X1) = k6_domain_1(u1_struct_0(sK0),X1) ) ),
    inference(subsumption_resolution,[],[f74,f63])).

fof(f63,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f61,f36])).

fof(f61,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f47,f37])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f74,plain,(
    ! [X1] :
      ( v1_xboole_0(u1_struct_0(sK0))
      | k1_tarski(X1) = k6_domain_1(u1_struct_0(sK0),X1)
      | ~ r2_hidden(X1,sK1) ) ),
    inference(resolution,[],[f57,f68])).

fof(f49,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(f55,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f234,plain,(
    ~ v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f233,f36])).

fof(f233,plain,
    ( v1_xboole_0(sK1)
    | ~ v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f232,f66])).

fof(f232,plain,(
    ~ r2_hidden(sK2(sK1),sK1) ),
    inference(resolution,[],[f231,f68])).

fof(f231,plain,(
    ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f230,f38])).

fof(f230,plain,
    ( ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f229,f41])).

fof(f229,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f228,f39])).

fof(f228,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f226,f217])).

fof(f226,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f49,f219])).

fof(f219,plain,(
    sK1 = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) ),
    inference(resolution,[],[f218,f192])).

fof(f192,plain,
    ( ~ v1_zfmisc_1(sK1)
    | sK1 = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) ),
    inference(backward_demodulation,[],[f78,f191])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n016.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 18:46:04 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (1743)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.21/0.48  % (1743)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f235,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(subsumption_resolution,[],[f234,f218])).
% 0.21/0.48  fof(f218,plain,(
% 0.21/0.48    v1_zfmisc_1(sK1)),
% 0.21/0.48    inference(resolution,[],[f217,f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,negated_conjecture,(
% 0.21/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.48    inference(negated_conjecture,[],[f12])).
% 0.21/0.48  fof(f12,conjecture,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).
% 0.21/0.48  fof(f217,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f216,f130])).
% 0.21/0.48  fof(f130,plain,(
% 0.21/0.48    l1_struct_0(sK3(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 0.21/0.48    inference(resolution,[],[f129,f45])).
% 0.21/0.48  fof(f45,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.48  fof(f129,plain,(
% 0.21/0.48    l1_pre_topc(sK3(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f122,f41])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    l1_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f122,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | l1_pre_topc(sK3(sK0,sK1))),
% 0.21/0.48    inference(resolution,[],[f120,f46])).
% 0.21/0.48  fof(f46,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 0.21/0.48  fof(f120,plain,(
% 0.21/0.48    m1_pre_topc(sK3(sK0,sK1),sK0) | ~v2_tex_2(sK1,sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f119,f38])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ~v2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f119,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | m1_pre_topc(sK3(sK0,sK1),sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f118,f36])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ~v1_xboole_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f118,plain,(
% 0.21/0.48    v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | m1_pre_topc(sK3(sK0,sK1),sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f117,f41])).
% 0.21/0.48  fof(f117,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | m1_pre_topc(sK3(sK0,sK1),sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f114,f39])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    v2_pre_topc(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f114,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | m1_pre_topc(sK3(sK0,sK1),sK0)),
% 0.21/0.48    inference(resolution,[],[f53,f37])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | m1_pre_topc(sK3(X0,X1),X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).
% 0.21/0.48  fof(f216,plain,(
% 0.21/0.48    ~l1_struct_0(sK3(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f215,f35])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | ~v1_zfmisc_1(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f215,plain,(
% 0.21/0.48    ~l1_struct_0(sK3(sK0,sK1)) | v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 0.21/0.48    inference(resolution,[],[f209,f128])).
% 0.21/0.48  fof(f128,plain,(
% 0.21/0.48    v7_struct_0(sK3(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f127,f102])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    v1_tdlat_3(sK3(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f101,f38])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK3(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f100,f36])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK3(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f99,f41])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK3(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f97,f39])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK3(sK0,sK1))),
% 0.21/0.48    inference(resolution,[],[f52,f37])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | v1_tdlat_3(sK3(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f127,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | ~v1_tdlat_3(sK3(sK0,sK1)) | v7_struct_0(sK3(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f126,f90])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    ~v2_struct_0(sK3(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 0.21/0.48    inference(subsumption_resolution,[],[f89,f38])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | ~v2_struct_0(sK3(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f88,f36])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | ~v2_struct_0(sK3(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f87,f41])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | ~v2_struct_0(sK3(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f85,f39])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | ~v2_struct_0(sK3(sK0,sK1))),
% 0.21/0.48    inference(resolution,[],[f50,f37])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | ~v2_struct_0(sK3(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f126,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | v2_struct_0(sK3(sK0,sK1)) | ~v1_tdlat_3(sK3(sK0,sK1)) | v7_struct_0(sK3(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f125,f38])).
% 0.21/0.48  fof(f125,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | v2_struct_0(sK0) | v2_struct_0(sK3(sK0,sK1)) | ~v1_tdlat_3(sK3(sK0,sK1)) | v7_struct_0(sK3(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f124,f41])).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(sK3(sK0,sK1)) | ~v1_tdlat_3(sK3(sK0,sK1)) | v7_struct_0(sK3(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f123,f40])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    v2_tdlat_3(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f123,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(sK3(sK0,sK1)) | ~v1_tdlat_3(sK3(sK0,sK1)) | v7_struct_0(sK3(sK0,sK1))),
% 0.21/0.48    inference(subsumption_resolution,[],[f121,f39])).
% 0.21/0.48  fof(f121,plain,(
% 0.21/0.48    ~v2_tex_2(sK1,sK0) | ~v2_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_struct_0(sK3(sK0,sK1)) | ~v1_tdlat_3(sK3(sK0,sK1)) | v7_struct_0(sK3(sK0,sK1))),
% 0.21/0.48    inference(resolution,[],[f120,f48])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_struct_0(X1) | ~v1_tdlat_3(X1) | v7_struct_0(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v7_struct_0(X1) & ~v2_struct_0(X1)) | ~v1_tdlat_3(X1) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (((v7_struct_0(X1) & ~v2_struct_0(X1)) | (~v1_tdlat_3(X1) | v2_struct_0(X1))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f8])).
% 0.21/0.49  fof(f8,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ((v1_tdlat_3(X1) & ~v2_struct_0(X1)) => (v7_struct_0(X1) & ~v2_struct_0(X1)))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc31_tex_2)).
% 0.21/0.49  fof(f209,plain,(
% 0.21/0.49    ~v7_struct_0(sK3(sK0,sK1)) | ~l1_struct_0(sK3(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 0.21/0.49    inference(superposition,[],[f55,f202])).
% 0.21/0.49  fof(f202,plain,(
% 0.21/0.49    sK1 = u1_struct_0(sK3(sK0,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f201,f138])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    v1_zfmisc_1(sK1) | sK1 = u1_struct_0(sK3(sK0,sK1))),
% 0.21/0.49    inference(resolution,[],[f137,f34])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK3(sK0,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f136,f38])).
% 0.21/0.49  fof(f136,plain,(
% 0.21/0.49    v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK3(sK0,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f135,f36])).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK3(sK0,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f134,f41])).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK3(sK0,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f131,f39])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK3(sK0,sK1))),
% 0.21/0.49    inference(resolution,[],[f54,f37])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | u1_struct_0(sK3(X0,X1)) = X1) )),
% 0.21/0.49    inference(cnf_transformation,[],[f25])).
% 0.21/0.49  fof(f201,plain,(
% 0.21/0.49    sK1 = u1_struct_0(sK3(sK0,sK1)) | ~v1_zfmisc_1(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f200,f36])).
% 0.21/0.49  fof(f200,plain,(
% 0.21/0.49    sK1 = u1_struct_0(sK3(sK0,sK1)) | v1_xboole_0(sK1) | ~v1_zfmisc_1(sK1)),
% 0.21/0.49    inference(resolution,[],[f199,f66])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    ( ! [X0] : (r2_hidden(sK2(X0),X0) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f65])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    ( ! [X0] : (v1_xboole_0(X0) | r2_hidden(sK2(X0),X0) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0)) )),
% 0.21/0.49    inference(resolution,[],[f56,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(sK2(X0),X0) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X0,X1) | v1_xboole_0(X1) | r2_hidden(X0,X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ! [X0,X1] : (r2_hidden(X0,X1) | v1_xboole_0(X1) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ! [X0,X1] : ((r2_hidden(X0,X1) | v1_xboole_0(X1)) | ~m1_subset_1(X0,X1))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,X1) => (r2_hidden(X0,X1) | v1_xboole_0(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_subset)).
% 0.21/0.49  fof(f199,plain,(
% 0.21/0.49    ~r2_hidden(sK2(sK1),sK1) | sK1 = u1_struct_0(sK3(sK0,sK1))),
% 0.21/0.49    inference(resolution,[],[f197,f68])).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    ( ! [X0] : (m1_subset_1(X0,u1_struct_0(sK0)) | ~r2_hidden(X0,sK1)) )),
% 0.21/0.49    inference(resolution,[],[f58,f37])).
% 0.21/0.49  fof(f58,plain,(
% 0.21/0.49    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.21/0.49    inference(flattening,[],[f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.21/0.49    inference(ennf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.21/0.49  fof(f197,plain,(
% 0.21/0.49    ~m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK3(sK0,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f195,f137])).
% 0.21/0.49  fof(f195,plain,(
% 0.21/0.49    v2_tex_2(sK1,sK0) | ~m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK3(sK0,sK1))),
% 0.21/0.49    inference(backward_demodulation,[],[f166,f191])).
% 0.21/0.49  fof(f191,plain,(
% 0.21/0.49    sK1 = k1_tarski(sK2(sK1))),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f183])).
% 0.21/0.49  fof(f183,plain,(
% 0.21/0.49    sK1 = k1_tarski(sK2(sK1)) | sK1 = k1_tarski(sK2(sK1)) | sK1 = k1_tarski(sK2(sK1))),
% 0.21/0.49    inference(superposition,[],[f175,f176])).
% 0.21/0.49  fof(f176,plain,(
% 0.21/0.49    sK1 = k6_domain_1(sK1,sK2(sK1)) | sK1 = k1_tarski(sK2(sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f174,f36])).
% 0.21/0.49  fof(f174,plain,(
% 0.21/0.49    sK1 = k1_tarski(sK2(sK1)) | sK1 = k6_domain_1(sK1,sK2(sK1)) | v1_xboole_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f171,f43])).
% 0.21/0.49  fof(f43,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_zfmisc_1(X0) | k6_domain_1(X0,sK2(X0)) = X0 | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f16])).
% 0.21/0.49  fof(f171,plain,(
% 0.21/0.49    v1_zfmisc_1(sK1) | sK1 = k1_tarski(sK2(sK1))),
% 0.21/0.49    inference(resolution,[],[f170,f34])).
% 0.21/0.49  fof(f170,plain,(
% 0.21/0.49    ~v2_tex_2(sK1,sK0) | sK1 = k1_tarski(sK2(sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f169,f130])).
% 0.21/0.49  fof(f169,plain,(
% 0.21/0.49    ~l1_struct_0(sK3(sK0,sK1)) | sK1 = k1_tarski(sK2(sK1)) | ~v2_tex_2(sK1,sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f168,f35])).
% 0.21/0.49  fof(f168,plain,(
% 0.21/0.49    ~l1_struct_0(sK3(sK0,sK1)) | v1_zfmisc_1(sK1) | sK1 = k1_tarski(sK2(sK1)) | ~v2_tex_2(sK1,sK0)),
% 0.21/0.49    inference(resolution,[],[f157,f128])).
% 0.21/0.49  fof(f157,plain,(
% 0.21/0.49    ~v7_struct_0(sK3(sK0,sK1)) | ~l1_struct_0(sK3(sK0,sK1)) | v1_zfmisc_1(sK1) | sK1 = k1_tarski(sK2(sK1))),
% 0.21/0.49    inference(superposition,[],[f55,f150])).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    sK1 = u1_struct_0(sK3(sK0,sK1)) | sK1 = k1_tarski(sK2(sK1))),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f146])).
% 0.21/0.49  fof(f146,plain,(
% 0.21/0.49    sK1 = k1_tarski(sK2(sK1)) | sK1 = u1_struct_0(sK3(sK0,sK1)) | sK1 = u1_struct_0(sK3(sK0,sK1))),
% 0.21/0.49    inference(superposition,[],[f142,f143])).
% 0.21/0.49  fof(f143,plain,(
% 0.21/0.49    sK1 = k6_domain_1(sK1,sK2(sK1)) | sK1 = u1_struct_0(sK3(sK0,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f141,f36])).
% 0.21/0.49  fof(f141,plain,(
% 0.21/0.49    sK1 = u1_struct_0(sK3(sK0,sK1)) | sK1 = k6_domain_1(sK1,sK2(sK1)) | v1_xboole_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f138,f43])).
% 0.21/0.49  fof(f142,plain,(
% 0.21/0.49    k1_tarski(sK2(sK1)) = k6_domain_1(sK1,sK2(sK1)) | sK1 = u1_struct_0(sK3(sK0,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f140,f36])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    sK1 = u1_struct_0(sK3(sK0,sK1)) | k1_tarski(sK2(sK1)) = k6_domain_1(sK1,sK2(sK1)) | v1_xboole_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f138,f75])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_zfmisc_1(X0) | k6_domain_1(X0,sK2(X0)) = k1_tarski(sK2(X0)) | v1_xboole_0(X0)) )),
% 0.21/0.49    inference(duplicate_literal_removal,[],[f73])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ( ! [X0] : (v1_xboole_0(X0) | k6_domain_1(X0,sK2(X0)) = k1_tarski(sK2(X0)) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0)) )),
% 0.21/0.49    inference(resolution,[],[f57,f42])).
% 0.21/0.49  fof(f57,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 0.21/0.49  fof(f175,plain,(
% 0.21/0.49    k1_tarski(sK2(sK1)) = k6_domain_1(sK1,sK2(sK1)) | sK1 = k1_tarski(sK2(sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f173,f36])).
% 0.21/0.49  fof(f173,plain,(
% 0.21/0.49    sK1 = k1_tarski(sK2(sK1)) | k1_tarski(sK2(sK1)) = k6_domain_1(sK1,sK2(sK1)) | v1_xboole_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f171,f75])).
% 0.21/0.49  fof(f166,plain,(
% 0.21/0.49    v2_tex_2(k1_tarski(sK2(sK1)),sK0) | ~m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK3(sK0,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f165,f38])).
% 0.21/0.49  fof(f165,plain,(
% 0.21/0.49    v2_tex_2(k1_tarski(sK2(sK1)),sK0) | ~m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | sK1 = u1_struct_0(sK3(sK0,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f164,f41])).
% 0.21/0.49  fof(f164,plain,(
% 0.21/0.49    v2_tex_2(k1_tarski(sK2(sK1)),sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | sK1 = u1_struct_0(sK3(sK0,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f162,f39])).
% 0.21/0.49  fof(f162,plain,(
% 0.21/0.49    v2_tex_2(k1_tarski(sK2(sK1)),sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | sK1 = u1_struct_0(sK3(sK0,sK1))),
% 0.21/0.49    inference(superposition,[],[f49,f139])).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    k1_tarski(sK2(sK1)) = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | sK1 = u1_struct_0(sK3(sK0,sK1))),
% 0.21/0.49    inference(resolution,[],[f138,f78])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ~v1_zfmisc_1(sK1) | k1_tarski(sK2(sK1)) = k6_domain_1(u1_struct_0(sK0),sK2(sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f77,f36])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    k1_tarski(sK2(sK1)) = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | v1_xboole_0(sK1) | ~v1_zfmisc_1(sK1)),
% 0.21/0.49    inference(resolution,[],[f76,f66])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ( ! [X1] : (~r2_hidden(X1,sK1) | k1_tarski(X1) = k6_domain_1(u1_struct_0(sK0),X1)) )),
% 0.21/0.49    inference(subsumption_resolution,[],[f74,f63])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ~v1_xboole_0(u1_struct_0(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f61,f36])).
% 0.21/0.49  fof(f61,plain,(
% 0.21/0.49    ~v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f47,f37])).
% 0.21/0.49  fof(f47,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.49  fof(f74,plain,(
% 0.21/0.49    ( ! [X1] : (v1_xboole_0(u1_struct_0(sK0)) | k1_tarski(X1) = k6_domain_1(u1_struct_0(sK0),X1) | ~r2_hidden(X1,sK1)) )),
% 0.21/0.49    inference(resolution,[],[f57,f68])).
% 0.21/0.49  fof(f49,plain,(
% 0.21/0.49    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f23])).
% 0.21/0.49  fof(f23,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f22])).
% 0.21/0.49  fof(f22,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f27])).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 0.21/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).
% 0.21/0.49  fof(f234,plain,(
% 0.21/0.49    ~v1_zfmisc_1(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f233,f36])).
% 0.21/0.49  fof(f233,plain,(
% 0.21/0.49    v1_xboole_0(sK1) | ~v1_zfmisc_1(sK1)),
% 0.21/0.49    inference(resolution,[],[f232,f66])).
% 0.21/0.49  fof(f232,plain,(
% 0.21/0.49    ~r2_hidden(sK2(sK1),sK1)),
% 0.21/0.49    inference(resolution,[],[f231,f68])).
% 0.21/0.49  fof(f231,plain,(
% 0.21/0.49    ~m1_subset_1(sK2(sK1),u1_struct_0(sK0))),
% 0.21/0.49    inference(subsumption_resolution,[],[f230,f38])).
% 0.21/0.49  fof(f230,plain,(
% 0.21/0.49    ~m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f229,f41])).
% 0.21/0.49  fof(f229,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | ~m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f228,f39])).
% 0.21/0.49  fof(f228,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f226,f217])).
% 0.21/0.49  fof(f226,plain,(
% 0.21/0.49    v2_tex_2(sK1,sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 0.21/0.49    inference(superposition,[],[f49,f219])).
% 0.21/0.49  fof(f219,plain,(
% 0.21/0.49    sK1 = k6_domain_1(u1_struct_0(sK0),sK2(sK1))),
% 0.21/0.49    inference(resolution,[],[f218,f192])).
% 0.21/0.49  fof(f192,plain,(
% 0.21/0.49    ~v1_zfmisc_1(sK1) | sK1 = k6_domain_1(u1_struct_0(sK0),sK2(sK1))),
% 0.21/0.49    inference(backward_demodulation,[],[f78,f191])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (1743)------------------------------
% 0.21/0.49  % (1743)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (1743)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (1743)Memory used [KB]: 6268
% 0.21/0.49  % (1743)Time elapsed: 0.015 s
% 0.21/0.49  % (1743)------------------------------
% 0.21/0.49  % (1743)------------------------------
% 0.21/0.49  % (1725)Success in time 0.125 s
%------------------------------------------------------------------------------
