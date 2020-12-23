%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:37 EST 2020

% Result     : Theorem 1.47s
% Output     : Refutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :  170 (5202 expanded)
%              Number of leaves         :   14 ( 918 expanded)
%              Depth                    :   44
%              Number of atoms          :  643 (31096 expanded)
%              Number of equality atoms :   73 ( 928 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f401,plain,(
    $false ),
    inference(global_subsumption,[],[f260,f386,f400])).

fof(f400,plain,(
    ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f399,f47])).

fof(f47,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

fof(f17,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f399,plain,
    ( ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f398,f50])).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f398,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f397,f48])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f397,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f395,f385])).

fof(f385,plain,(
    ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f384,f234])).

fof(f234,plain,
    ( l1_struct_0(sK4(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f227,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f227,plain,
    ( l1_pre_topc(sK4(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f223,f50])).

fof(f223,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | l1_pre_topc(sK4(sK0,sK1)) ),
    inference(resolution,[],[f218,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | l1_pre_topc(X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).

fof(f218,plain,
    ( m1_pre_topc(sK4(sK0,sK1),sK0)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f217,f47])).

fof(f217,plain,
    ( v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | m1_pre_topc(sK4(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f216,f45])).

fof(f45,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f216,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | m1_pre_topc(sK4(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f215,f50])).

fof(f215,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | m1_pre_topc(sK4(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f212,f48])).

fof(f212,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | m1_pre_topc(sK4(sK0,sK1),sK0) ),
    inference(resolution,[],[f70,f46])).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | m1_pre_topc(sK4(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f384,plain,
    ( ~ l1_struct_0(sK4(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f383,f44])).

fof(f44,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f383,plain,
    ( ~ l1_struct_0(sK4(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f372,f232])).

fof(f232,plain,
    ( v7_struct_0(sK4(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f231,f227])).

fof(f231,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK4(sK0,sK1))
    | v7_struct_0(sK4(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f230,f206])).

fof(f206,plain,
    ( v1_tdlat_3(sK4(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f205,f47])).

fof(f205,plain,
    ( v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK4(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f204,f45])).

fof(f204,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK4(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f203,f50])).

fof(f203,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK4(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f200,f48])).

fof(f200,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v1_tdlat_3(sK4(sK0,sK1)) ),
    inference(resolution,[],[f69,f46])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | v1_tdlat_3(sK4(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f230,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v1_tdlat_3(sK4(sK0,sK1))
    | ~ l1_pre_topc(sK4(sK0,sK1))
    | v7_struct_0(sK4(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f228,f186])).

fof(f186,plain,
    ( ~ v2_struct_0(sK4(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f185,f47])).

fof(f185,plain,
    ( v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v2_struct_0(sK4(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f184,f45])).

fof(f184,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v2_struct_0(sK4(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f183,f50])).

fof(f183,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v2_struct_0(sK4(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f180,f48])).

fof(f180,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | ~ v2_struct_0(sK4(sK0,sK1)) ),
    inference(resolution,[],[f67,f46])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | ~ v2_struct_0(sK4(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f228,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK4(sK0,sK1))
    | ~ v1_tdlat_3(sK4(sK0,sK1))
    | ~ l1_pre_topc(sK4(sK0,sK1))
    | v7_struct_0(sK4(sK0,sK1)) ),
    inference(resolution,[],[f226,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v7_struct_0(X0) ) ),
    inference(subsumption_resolution,[],[f57,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v2_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_tdlat_3(X0)
      | v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v2_pre_topc(X0)
        & v7_struct_0(X0)
        & ~ v2_struct_0(X0) )
      | ~ v2_tdlat_3(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( ( v2_tdlat_3(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ( v2_pre_topc(X0)
          & v7_struct_0(X0)
          & ~ v2_struct_0(X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_1)).

fof(f226,plain,
    ( v2_tdlat_3(sK4(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f225,f47])).

fof(f225,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v2_struct_0(sK0)
    | v2_tdlat_3(sK4(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f224,f50])).

fof(f224,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_tdlat_3(sK4(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f222,f49])).

fof(f49,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f222,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_tdlat_3(sK4(sK0,sK1)) ),
    inference(resolution,[],[f218,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_tdlat_3(X1) ) ),
    inference(subsumption_resolution,[],[f65,f56])).

fof(f65,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v2_tdlat_3(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tdlat_3(X1)
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => v2_tdlat_3(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tdlat_3)).

fof(f372,plain,
    ( ~ v7_struct_0(sK4(sK0,sK1))
    | ~ l1_struct_0(sK4(sK0,sK1))
    | v1_zfmisc_1(sK1) ),
    inference(superposition,[],[f72,f360])).

fof(f360,plain,(
    sK1 = u1_struct_0(sK4(sK0,sK1)) ),
    inference(global_subsumption,[],[f260,f285,f359])).

fof(f359,plain,
    ( ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK4(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f358,f281])).

fof(f281,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK4(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f280,f47])).

fof(f280,plain,
    ( v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK4(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f279,f45])).

fof(f279,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK4(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f278,f50])).

fof(f278,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK4(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f275,f48])).

fof(f275,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK4(sK0,sK1)) ),
    inference(resolution,[],[f71,f46])).

% (17121)Refutation not found, incomplete strategy% (17121)------------------------------
% (17121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17121)Termination reason: Refutation not found, incomplete strategy

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_tex_2(X1,X0)
      | u1_struct_0(sK4(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f38])).

% (17121)Memory used [KB]: 10618
fof(f358,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK4(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f357,f47])).

% (17121)Time elapsed: 0.101 s
% (17121)------------------------------
% (17121)------------------------------
fof(f357,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | sK1 = u1_struct_0(sK4(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f356,f50])).

fof(f356,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | sK1 = u1_struct_0(sK4(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f354,f48])).

fof(f354,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | sK1 = u1_struct_0(sK4(sK0,sK1)) ),
    inference(superposition,[],[f66,f350])).

fof(f350,plain,
    ( sK1 = k6_domain_1(u1_struct_0(sK0),sK2(sK1))
    | sK1 = u1_struct_0(sK4(sK0,sK1)) ),
    inference(backward_demodulation,[],[f286,f346])).

fof(f346,plain,(
    sK1 = k1_tarski(sK2(sK1)) ),
    inference(duplicate_literal_removal,[],[f337])).

fof(f337,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | sK1 = k1_tarski(sK2(sK1))
    | sK1 = k1_tarski(sK2(sK1)) ),
    inference(superposition,[],[f328,f329])).

fof(f329,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | sK1 = k1_tarski(sK2(sK1)) ),
    inference(subsumption_resolution,[],[f327,f45])).

fof(f327,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | sK1 = k6_domain_1(sK1,sK2(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f324,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | k6_domain_1(X0,sK2(X0)) = X0
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ( v1_zfmisc_1(X0)
      <=> ? [X1] :
            ( k6_domain_1(X0,X1) = X0
            & m1_subset_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).

fof(f324,plain,
    ( v1_zfmisc_1(sK1)
    | sK1 = k1_tarski(sK2(sK1)) ),
    inference(resolution,[],[f323,f43])).

fof(f43,plain,
    ( v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f323,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | sK1 = k1_tarski(sK2(sK1)) ),
    inference(subsumption_resolution,[],[f322,f234])).

fof(f322,plain,
    ( ~ l1_struct_0(sK4(sK0,sK1))
    | sK1 = k1_tarski(sK2(sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f321,f44])).

fof(f321,plain,
    ( ~ l1_struct_0(sK4(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | sK1 = k1_tarski(sK2(sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f311,f232])).

fof(f311,plain,
    ( ~ v7_struct_0(sK4(sK0,sK1))
    | ~ l1_struct_0(sK4(sK0,sK1))
    | v1_zfmisc_1(sK1)
    | sK1 = k1_tarski(sK2(sK1)) ),
    inference(superposition,[],[f72,f299])).

fof(f299,plain,
    ( sK1 = u1_struct_0(sK4(sK0,sK1))
    | sK1 = k1_tarski(sK2(sK1)) ),
    inference(duplicate_literal_removal,[],[f294])).

fof(f294,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | sK1 = u1_struct_0(sK4(sK0,sK1))
    | sK1 = u1_struct_0(sK4(sK0,sK1)) ),
    inference(superposition,[],[f289,f290])).

fof(f290,plain,
    ( sK1 = k6_domain_1(sK1,sK2(sK1))
    | sK1 = u1_struct_0(sK4(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f288,f45])).

fof(f288,plain,
    ( sK1 = u1_struct_0(sK4(sK0,sK1))
    | sK1 = k6_domain_1(sK1,sK2(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f285,f52])).

fof(f289,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | sK1 = u1_struct_0(sK4(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f287,f45])).

fof(f287,plain,
    ( sK1 = u1_struct_0(sK4(sK0,sK1))
    | k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f285,f88])).

fof(f88,plain,(
    ! [X0] :
      ( ~ v1_zfmisc_1(X0)
      | k6_domain_1(X0,sK2(X0)) = k1_tarski(sK2(X0))
      | v1_xboole_0(X0) ) ),
    inference(duplicate_literal_removal,[],[f87])).

fof(f87,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | k6_domain_1(X0,sK2(X0)) = k1_tarski(sK2(X0))
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(resolution,[],[f73,f51])).

fof(f51,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(X0),X0)
      | v1_xboole_0(X0)
      | ~ v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0)
      | k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k6_domain_1(X0,X1) = k1_tarski(X1)
      | ~ m1_subset_1(X1,X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,X0)
        & ~ v1_xboole_0(X0) )
     => k6_domain_1(X0,X1) = k1_tarski(X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).

fof(f328,plain,
    ( k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | sK1 = k1_tarski(sK2(sK1)) ),
    inference(subsumption_resolution,[],[f326,f45])).

fof(f326,plain,
    ( sK1 = k1_tarski(sK2(sK1))
    | k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f324,f88])).

fof(f286,plain,
    ( sK1 = u1_struct_0(sK4(sK0,sK1))
    | k6_domain_1(u1_struct_0(sK0),sK2(sK1)) = k1_tarski(sK2(sK1)) ),
    inference(resolution,[],[f285,f169])).

fof(f169,plain,
    ( ~ v1_zfmisc_1(sK1)
    | k6_domain_1(u1_struct_0(sK0),sK2(sK1)) = k1_tarski(sK2(sK1)) ),
    inference(subsumption_resolution,[],[f168,f45])).

fof(f168,plain,
    ( k6_domain_1(u1_struct_0(sK0),sK2(sK1)) = k1_tarski(sK2(sK1))
    | v1_xboole_0(sK1)
    | ~ v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f167,f51])).

fof(f167,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK1)
      | k6_domain_1(u1_struct_0(sK0),X2) = k1_tarski(X2) ) ),
    inference(subsumption_resolution,[],[f165,f81])).

fof(f81,plain,(
    ~ v1_xboole_0(u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f79,f45])).

fof(f79,plain,
    ( ~ v1_xboole_0(u1_struct_0(sK0))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f59,f46])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f165,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,sK1)
      | v1_xboole_0(u1_struct_0(sK0))
      | k6_domain_1(u1_struct_0(sK0),X2) = k1_tarski(X2) ) ),
    inference(resolution,[],[f163,f73])).

fof(f163,plain,(
    ! [X0] :
      ( m1_subset_1(X0,u1_struct_0(sK0))
      | ~ m1_subset_1(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f162,f47])).

fof(f162,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,sK1)
      | v2_struct_0(sK0)
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f161,f50])).

fof(f161,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,sK1)
      | v2_struct_0(sK0)
      | m1_subset_1(X0,u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f160,f104])).

fof(f104,plain,(
    m1_pre_topc(sK3(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f103,f47])).

fof(f103,plain,
    ( v2_struct_0(sK0)
    | m1_pre_topc(sK3(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f102,f45])).

fof(f102,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK3(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f100,f50])).

fof(f100,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | m1_pre_topc(sK3(sK0,sK1),sK0) ),
    inference(resolution,[],[f62,f46])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | m1_pre_topc(sK3(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
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
    inference(flattening,[],[f29])).

fof(f29,plain,(
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
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
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

fof(f160,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(sK3(sK0,sK1),X1)
      | ~ l1_pre_topc(X1)
      | ~ m1_subset_1(X0,sK1)
      | v2_struct_0(X1)
      | m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f159,f94])).

fof(f94,plain,(
    ~ v2_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f93,f47])).

fof(f93,plain,
    ( v2_struct_0(sK0)
    | ~ v2_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f92,f45])).

fof(f92,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f90,f50])).

fof(f90,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v2_struct_0(sK3(sK0,sK1)) ),
    inference(resolution,[],[f60,f46])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v2_struct_0(sK3(X0,X1)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f159,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,sK1)
      | ~ l1_pre_topc(X1)
      | v2_struct_0(sK3(sK0,sK1))
      | ~ m1_pre_topc(sK3(sK0,sK1),X1)
      | v2_struct_0(X1)
      | m1_subset_1(X0,u1_struct_0(X1)) ) ),
    inference(superposition,[],[f64,f123])).

fof(f123,plain,(
    sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f122,f47])).

fof(f122,plain,
    ( v2_struct_0(sK0)
    | sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f121,f45])).

fof(f121,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f119,f50])).

fof(f119,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | sK1 = u1_struct_0(sK3(sK0,sK1)) ),
    inference(resolution,[],[f63,f46])).

fof(f63,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | u1_struct_0(sK3(X0,X1)) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

% (17123)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% (17128)Refutation not found, incomplete strategy% (17128)------------------------------
% (17128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (17128)Termination reason: Refutation not found, incomplete strategy

% (17128)Memory used [KB]: 1791
% (17128)Time elapsed: 0.136 s
% (17128)------------------------------
% (17128)------------------------------
fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | m1_subset_1(X2,u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,u1_struct_0(X0))
              | ~ m1_subset_1(X2,u1_struct_0(X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,u1_struct_0(X0))
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)
          | ~ m1_subset_1(X1,u1_struct_0(X0)) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,u1_struct_0(X0))
         => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).

fof(f285,plain,
    ( v1_zfmisc_1(sK1)
    | sK1 = u1_struct_0(sK4(sK0,sK1)) ),
    inference(resolution,[],[f281,f43])).

fof(f72,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( v1_zfmisc_1(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | ~ v7_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & v7_struct_0(X0) )
     => v1_zfmisc_1(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).

fof(f395,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0) ),
    inference(superposition,[],[f66,f387])).

fof(f387,plain,(
    sK1 = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) ),
    inference(resolution,[],[f386,f347])).

fof(f347,plain,
    ( ~ v1_zfmisc_1(sK1)
    | sK1 = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) ),
    inference(backward_demodulation,[],[f169,f346])).

fof(f386,plain,(
    v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f385,f43])).

fof(f260,plain,
    ( m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | ~ v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f259,f50])).

fof(f259,plain,
    ( m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f258,f47])).

fof(f258,plain,
    ( m1_subset_1(sK2(sK1),u1_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f255,f104])).

fof(f255,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(sK3(sK0,sK1),X0)
      | m1_subset_1(sK2(sK1),u1_struct_0(X0))
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_zfmisc_1(sK1) ) ),
    inference(subsumption_resolution,[],[f254,f45])).

fof(f254,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(sK1),u1_struct_0(X0))
      | ~ m1_pre_topc(sK3(sK0,sK1),X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(sK1)
      | ~ v1_zfmisc_1(sK1) ) ),
    inference(subsumption_resolution,[],[f250,f94])).

fof(f250,plain,(
    ! [X0] :
      ( m1_subset_1(sK2(sK1),u1_struct_0(X0))
      | v2_struct_0(sK3(sK0,sK1))
      | ~ m1_pre_topc(sK3(sK0,sK1),X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(sK1)
      | ~ v1_zfmisc_1(sK1) ) ),
    inference(superposition,[],[f158,f123])).

fof(f158,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(u1_struct_0(X1)),u1_struct_0(X0))
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(u1_struct_0(X1))
      | ~ v1_zfmisc_1(u1_struct_0(X1)) ) ),
    inference(resolution,[],[f64,f51])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n012.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:20:07 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (17116)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_20 on theBenchmark
% 0.22/0.50  % (17113)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_118 on theBenchmark
% 0.22/0.51  % (17131)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_172 on theBenchmark
% 0.22/0.51  % (17114)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_22 on theBenchmark
% 0.22/0.51  % (17110)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_18 on theBenchmark
% 0.22/0.51  % (17134)lrs+1011_7_afp=100000:afq=1.0:amm=sco:anc=all_dependent:bs=unit_only:bsr=on:ep=RS:fde=none:gsp=input_only:gs=on:gsem=off:lwlo=on:nm=4:nwc=1:stl=120:sos=theory:sp=occurrence:uhcvi=on_412 on theBenchmark
% 0.22/0.51  % (17126)ott+1011_4:1_add=off:afr=on:afp=10000:afq=1.0:anc=none:bd=preordered:cond=fast:nm=32:newcnf=on:nwc=1.2:sas=z3:sac=on:sp=occurrence:urr=on:updr=off_122 on theBenchmark
% 0.22/0.51  % (17119)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_71 on theBenchmark
% 0.22/0.51  % (17120)lrs+11_5_av=off:cond=on:fsr=off:lma=on:lwlo=on:nwc=1.2:sas=z3:stl=30:sp=reverse_arity:updr=off_142 on theBenchmark
% 0.22/0.52  % (17119)Refutation not found, incomplete strategy% (17119)------------------------------
% 0.22/0.52  % (17119)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17125)lrs+11_5_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bsr=on:cond=on:fsr=off:gs=on:gsem=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on:updr=off_18 on theBenchmark
% 0.22/0.52  % (17117)lrs+1011_4:1_acc=model:add=large:afp=40000:afq=1.4:ccuc=first:cond=on:fsr=off:gsp=input_only:gs=on:gsem=off:irw=on:nwc=1:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:urr=on_42 on theBenchmark
% 0.22/0.52  % (17124)lrs+10_128_av=off:bs=on:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=2:newcnf=on:nwc=1:stl=30:updr=off_207 on theBenchmark
% 0.22/0.52  % (17114)Refutation not found, incomplete strategy% (17114)------------------------------
% 0.22/0.52  % (17114)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17114)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (17114)Memory used [KB]: 10618
% 0.22/0.52  % (17114)Time elapsed: 0.100 s
% 0.22/0.52  % (17114)------------------------------
% 0.22/0.52  % (17114)------------------------------
% 0.22/0.52  % (17127)ott+10_1_av=off:bd=off:bsr=on:cond=on:fsr=off:irw=on:nm=2:nwc=1:sd=3:ss=axioms:sos=on:sp=occurrence:urr=on_19 on theBenchmark
% 0.22/0.52  % (17118)dis+11_5:4_acc=on:add=large:afp=40000:afq=1.2:amm=sco:anc=all_dependent:bd=off:ccuc=small_ones:irw=on:lcm=reverse:lma=on:nwc=1:sd=3:ss=axioms:sos=all:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.52  % (17111)lrs+4_14_afr=on:afp=4000:afq=1.1:anc=none:cond=on:gs=on:gsem=on:irw=on:lma=on:nm=6:nwc=1.1:sas=z3:stl=30:sd=4:ss=axioms:st=1.2:sos=all:updr=off_51 on theBenchmark
% 0.22/0.52  % (17118)Refutation not found, incomplete strategy% (17118)------------------------------
% 0.22/0.52  % (17118)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (17129)lrs+1011_3_afp=1000:afq=1.1:anc=none:bd=off:cond=on:fsr=off:gs=on:gsem=off:irw=on:nm=6:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=2.0:sac=on:urr=on_174 on theBenchmark
% 0.22/0.52  % (17122)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_136 on theBenchmark
% 0.22/0.52  % (17133)dis+1011_5:1_add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:bs=unit_only:bce=on:ep=RS:fsr=off:fde=none:irw=on:lwlo=on:nwc=1:sas=z3:sos=theory:sac=on:updr=off:uhcvi=on_398 on theBenchmark
% 0.22/0.52  % (17119)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (17119)Memory used [KB]: 10618
% 0.22/0.52  % (17119)Time elapsed: 0.091 s
% 0.22/0.52  % (17119)------------------------------
% 0.22/0.52  % (17119)------------------------------
% 0.22/0.52  % (17121)lrs-1_2:3_add=large:afr=on:afp=1000:afq=2.0:amm=sco:anc=none:bs=unit_only:bsr=on:cond=on:fsr=off:gs=on:nm=16:nwc=1:stl=30:sd=1:ss=axioms:sos=on:sac=on_12 on theBenchmark
% 0.22/0.53  % (17127)Refutation not found, incomplete strategy% (17127)------------------------------
% 0.22/0.53  % (17127)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (17127)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (17127)Memory used [KB]: 1663
% 0.22/0.53  % (17127)Time elapsed: 0.112 s
% 0.22/0.53  % (17127)------------------------------
% 0.22/0.53  % (17127)------------------------------
% 0.22/0.53  % (17134)Refutation not found, incomplete strategy% (17134)------------------------------
% 0.22/0.53  % (17134)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.53  % (17134)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (17134)Memory used [KB]: 10618
% 0.22/0.53  % (17134)Time elapsed: 0.060 s
% 0.22/0.53  % (17134)------------------------------
% 0.22/0.53  % (17134)------------------------------
% 0.22/0.53  % (17132)ott+11_8:1_av=off:fde=unused:nm=2:newcnf=on:nwc=1:sd=2:ss=axioms:st=3.0:sos=all:sp=reverse_arity:updr=off:uhcvi=on_70 on theBenchmark
% 0.22/0.53  % (17118)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (17118)Memory used [KB]: 6140
% 0.22/0.53  % (17118)Time elapsed: 0.064 s
% 0.22/0.53  % (17118)------------------------------
% 0.22/0.53  % (17118)------------------------------
% 0.22/0.53  % (17130)lrs+1011_1024_av=off:bsr=on:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=32:nwc=1:stl=90:sp=reverse_arity:uhcvi=on_426 on theBenchmark
% 0.22/0.53  % (17128)dis+11_1_av=off:gsp=input_only:lma=on:nm=4:nwc=1:sd=2:ss=axioms:st=5.0:sos=all:sp=occurrence:urr=on_246 on theBenchmark
% 0.22/0.54  % (17115)lrs+1010_32_afr=on:anc=none:bd=off:fsr=off:gs=on:gsem=on:nwc=1.3:nicw=on:sas=z3:stl=30:updr=off_63 on theBenchmark
% 0.22/0.54  % (17131)Refutation not found, incomplete strategy% (17131)------------------------------
% 0.22/0.54  % (17131)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.54  % (17131)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.54  
% 0.22/0.54  % (17131)Memory used [KB]: 6268
% 0.22/0.54  % (17131)Time elapsed: 0.118 s
% 0.22/0.54  % (17131)------------------------------
% 0.22/0.54  % (17131)------------------------------
% 1.47/0.54  % (17124)Refutation found. Thanks to Tanya!
% 1.47/0.54  % SZS status Theorem for theBenchmark
% 1.47/0.54  % SZS output start Proof for theBenchmark
% 1.47/0.54  fof(f401,plain,(
% 1.47/0.54    $false),
% 1.47/0.54    inference(global_subsumption,[],[f260,f386,f400])).
% 1.47/0.54  fof(f400,plain,(
% 1.47/0.54    ~m1_subset_1(sK2(sK1),u1_struct_0(sK0))),
% 1.47/0.54    inference(subsumption_resolution,[],[f399,f47])).
% 1.47/0.54  fof(f47,plain,(
% 1.47/0.54    ~v2_struct_0(sK0)),
% 1.47/0.54    inference(cnf_transformation,[],[f18])).
% 1.47/0.54  fof(f18,plain,(
% 1.47/0.54    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.47/0.54    inference(flattening,[],[f17])).
% 1.47/0.54  fof(f17,plain,(
% 1.47/0.54    ? [X0] : (? [X1] : ((v2_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.47/0.54    inference(ennf_transformation,[],[f16])).
% 1.47/0.54  fof(f16,negated_conjecture,(
% 1.47/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.47/0.54    inference(negated_conjecture,[],[f15])).
% 1.47/0.54  fof(f15,conjecture,(
% 1.47/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 1.47/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).
% 1.47/0.54  fof(f399,plain,(
% 1.47/0.54    ~m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 1.47/0.54    inference(subsumption_resolution,[],[f398,f50])).
% 1.47/0.54  fof(f50,plain,(
% 1.47/0.54    l1_pre_topc(sK0)),
% 1.47/0.54    inference(cnf_transformation,[],[f18])).
% 1.47/0.54  fof(f398,plain,(
% 1.47/0.54    ~l1_pre_topc(sK0) | ~m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 1.47/0.54    inference(subsumption_resolution,[],[f397,f48])).
% 1.47/0.54  fof(f48,plain,(
% 1.47/0.54    v2_pre_topc(sK0)),
% 1.47/0.54    inference(cnf_transformation,[],[f18])).
% 1.47/0.54  fof(f397,plain,(
% 1.47/0.54    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 1.47/0.54    inference(subsumption_resolution,[],[f395,f385])).
% 1.47/0.54  fof(f385,plain,(
% 1.47/0.54    ~v2_tex_2(sK1,sK0)),
% 1.47/0.54    inference(subsumption_resolution,[],[f384,f234])).
% 1.47/0.54  fof(f234,plain,(
% 1.47/0.54    l1_struct_0(sK4(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 1.47/0.54    inference(resolution,[],[f227,f54])).
% 1.47/0.54  fof(f54,plain,(
% 1.47/0.54    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.47/0.54    inference(cnf_transformation,[],[f20])).
% 1.47/0.54  fof(f20,plain,(
% 1.47/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.47/0.54    inference(ennf_transformation,[],[f2])).
% 1.47/0.54  fof(f2,axiom,(
% 1.47/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.47/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.47/0.54  fof(f227,plain,(
% 1.47/0.54    l1_pre_topc(sK4(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 1.47/0.54    inference(subsumption_resolution,[],[f223,f50])).
% 1.47/0.54  fof(f223,plain,(
% 1.47/0.54    ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | l1_pre_topc(sK4(sK0,sK1))),
% 1.47/0.54    inference(resolution,[],[f218,f58])).
% 1.47/0.54  fof(f58,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | l1_pre_topc(X1)) )),
% 1.47/0.54    inference(cnf_transformation,[],[f27])).
% 1.47/0.54  fof(f27,plain,(
% 1.47/0.54    ! [X0] : (! [X1] : (l1_pre_topc(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.47/0.54    inference(ennf_transformation,[],[f3])).
% 1.47/0.54  fof(f3,axiom,(
% 1.47/0.54    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => l1_pre_topc(X1)))),
% 1.47/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_m1_pre_topc)).
% 1.47/0.54  fof(f218,plain,(
% 1.47/0.54    m1_pre_topc(sK4(sK0,sK1),sK0) | ~v2_tex_2(sK1,sK0)),
% 1.47/0.54    inference(subsumption_resolution,[],[f217,f47])).
% 1.47/0.54  fof(f217,plain,(
% 1.47/0.54    v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | m1_pre_topc(sK4(sK0,sK1),sK0)),
% 1.47/0.54    inference(subsumption_resolution,[],[f216,f45])).
% 1.47/0.54  fof(f45,plain,(
% 1.47/0.54    ~v1_xboole_0(sK1)),
% 1.47/0.54    inference(cnf_transformation,[],[f18])).
% 1.47/0.54  fof(f216,plain,(
% 1.47/0.54    v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | m1_pre_topc(sK4(sK0,sK1),sK0)),
% 1.47/0.54    inference(subsumption_resolution,[],[f215,f50])).
% 1.47/0.54  fof(f215,plain,(
% 1.47/0.54    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | m1_pre_topc(sK4(sK0,sK1),sK0)),
% 1.47/0.54    inference(subsumption_resolution,[],[f212,f48])).
% 1.47/0.54  fof(f212,plain,(
% 1.47/0.54    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | m1_pre_topc(sK4(sK0,sK1),sK0)),
% 1.47/0.54    inference(resolution,[],[f70,f46])).
% 1.47/0.54  fof(f46,plain,(
% 1.47/0.54    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.47/0.54    inference(cnf_transformation,[],[f18])).
% 1.47/0.54  fof(f70,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | m1_pre_topc(sK4(X0,X1),X0)) )),
% 1.47/0.54    inference(cnf_transformation,[],[f38])).
% 1.47/0.54  fof(f38,plain,(
% 1.47/0.54    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.54    inference(flattening,[],[f37])).
% 1.47/0.54  fof(f37,plain,(
% 1.47/0.54    ! [X0] : (! [X1] : ((? [X2] : (u1_struct_0(X2) = X1 & (m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2))) | ~v2_tex_2(X1,X0)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.47/0.54    inference(ennf_transformation,[],[f13])).
% 1.47/0.54  fof(f13,axiom,(
% 1.47/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ~(! [X2] : ((m1_pre_topc(X2,X0) & v1_tdlat_3(X2) & v1_pre_topc(X2) & ~v2_struct_0(X2)) => u1_struct_0(X2) != X1) & v2_tex_2(X1,X0))))),
% 1.47/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_tex_2)).
% 1.47/0.54  fof(f384,plain,(
% 1.47/0.54    ~l1_struct_0(sK4(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 1.47/0.54    inference(subsumption_resolution,[],[f383,f44])).
% 1.47/0.54  fof(f44,plain,(
% 1.47/0.54    ~v2_tex_2(sK1,sK0) | ~v1_zfmisc_1(sK1)),
% 1.47/0.54    inference(cnf_transformation,[],[f18])).
% 1.47/0.54  fof(f383,plain,(
% 1.47/0.54    ~l1_struct_0(sK4(sK0,sK1)) | v1_zfmisc_1(sK1) | ~v2_tex_2(sK1,sK0)),
% 1.47/0.54    inference(resolution,[],[f372,f232])).
% 1.47/0.54  fof(f232,plain,(
% 1.47/0.54    v7_struct_0(sK4(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 1.47/0.54    inference(subsumption_resolution,[],[f231,f227])).
% 1.47/0.54  fof(f231,plain,(
% 1.47/0.54    ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK4(sK0,sK1)) | v7_struct_0(sK4(sK0,sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f230,f206])).
% 1.47/0.54  fof(f206,plain,(
% 1.47/0.54    v1_tdlat_3(sK4(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 1.47/0.54    inference(subsumption_resolution,[],[f205,f47])).
% 1.47/0.54  fof(f205,plain,(
% 1.47/0.54    v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK4(sK0,sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f204,f45])).
% 1.47/0.54  fof(f204,plain,(
% 1.47/0.54    v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK4(sK0,sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f203,f50])).
% 1.47/0.54  fof(f203,plain,(
% 1.47/0.54    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK4(sK0,sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f200,f48])).
% 1.47/0.54  fof(f200,plain,(
% 1.47/0.54    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | v1_tdlat_3(sK4(sK0,sK1))),
% 1.47/0.54    inference(resolution,[],[f69,f46])).
% 1.47/0.54  fof(f69,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | v1_tdlat_3(sK4(X0,X1))) )),
% 1.47/0.54    inference(cnf_transformation,[],[f38])).
% 1.47/0.54  fof(f230,plain,(
% 1.47/0.54    ~v2_tex_2(sK1,sK0) | ~v1_tdlat_3(sK4(sK0,sK1)) | ~l1_pre_topc(sK4(sK0,sK1)) | v7_struct_0(sK4(sK0,sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f228,f186])).
% 1.47/0.54  fof(f186,plain,(
% 1.47/0.54    ~v2_struct_0(sK4(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 1.47/0.54    inference(subsumption_resolution,[],[f185,f47])).
% 1.47/0.54  fof(f185,plain,(
% 1.47/0.54    v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | ~v2_struct_0(sK4(sK0,sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f184,f45])).
% 1.47/0.54  fof(f184,plain,(
% 1.47/0.54    v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | ~v2_struct_0(sK4(sK0,sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f183,f50])).
% 1.47/0.54  fof(f183,plain,(
% 1.47/0.54    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | ~v2_struct_0(sK4(sK0,sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f180,f48])).
% 1.47/0.54  fof(f180,plain,(
% 1.47/0.54    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | ~v2_struct_0(sK4(sK0,sK1))),
% 1.47/0.54    inference(resolution,[],[f67,f46])).
% 1.47/0.54  fof(f67,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | ~v2_struct_0(sK4(X0,X1))) )),
% 1.47/0.54    inference(cnf_transformation,[],[f38])).
% 1.47/0.54  fof(f228,plain,(
% 1.47/0.54    ~v2_tex_2(sK1,sK0) | v2_struct_0(sK4(sK0,sK1)) | ~v1_tdlat_3(sK4(sK0,sK1)) | ~l1_pre_topc(sK4(sK0,sK1)) | v7_struct_0(sK4(sK0,sK1))),
% 1.47/0.54    inference(resolution,[],[f226,f74])).
% 1.47/0.54  fof(f74,plain,(
% 1.47/0.54    ( ! [X0] : (~v2_tdlat_3(X0) | v2_struct_0(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v7_struct_0(X0)) )),
% 1.47/0.54    inference(subsumption_resolution,[],[f57,f56])).
% 1.47/0.54  fof(f56,plain,(
% 1.47/0.54    ( ! [X0] : (~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_pre_topc(X0)) )),
% 1.47/0.54    inference(cnf_transformation,[],[f24])).
% 1.47/0.54  fof(f24,plain,(
% 1.47/0.54    ! [X0] : (v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 1.47/0.54    inference(flattening,[],[f23])).
% 1.47/0.54  fof(f23,plain,(
% 1.47/0.54    ! [X0] : ((v2_pre_topc(X0) | ~v2_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 1.47/0.54    inference(ennf_transformation,[],[f8])).
% 1.47/0.54  fof(f8,axiom,(
% 1.47/0.54    ! [X0] : (l1_pre_topc(X0) => (v2_tdlat_3(X0) => v2_pre_topc(X0)))),
% 1.47/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tdlat_3)).
% 1.47/0.54  fof(f57,plain,(
% 1.47/0.54    ( ! [X0] : (~l1_pre_topc(X0) | v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_tdlat_3(X0) | v7_struct_0(X0)) )),
% 1.47/0.54    inference(cnf_transformation,[],[f26])).
% 1.47/0.54  fof(f26,plain,(
% 1.47/0.54    ! [X0] : ((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | ~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.47/0.54    inference(flattening,[],[f25])).
% 1.47/0.54  fof(f25,plain,(
% 1.47/0.54    ! [X0] : (((v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0)) | (~v2_tdlat_3(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))) | ~l1_pre_topc(X0))),
% 1.47/0.54    inference(ennf_transformation,[],[f9])).
% 1.47/0.54  fof(f9,axiom,(
% 1.47/0.54    ! [X0] : (l1_pre_topc(X0) => ((v2_tdlat_3(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(X0) & v7_struct_0(X0) & ~v2_struct_0(X0))))),
% 1.47/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_tex_1)).
% 1.47/0.54  fof(f226,plain,(
% 1.47/0.54    v2_tdlat_3(sK4(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 1.47/0.54    inference(subsumption_resolution,[],[f225,f47])).
% 1.47/0.54  fof(f225,plain,(
% 1.47/0.54    ~v2_tex_2(sK1,sK0) | v2_struct_0(sK0) | v2_tdlat_3(sK4(sK0,sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f224,f50])).
% 1.47/0.54  fof(f224,plain,(
% 1.47/0.54    ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_tdlat_3(sK4(sK0,sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f222,f49])).
% 1.47/0.54  fof(f49,plain,(
% 1.47/0.54    v2_tdlat_3(sK0)),
% 1.47/0.54    inference(cnf_transformation,[],[f18])).
% 1.47/0.54  fof(f222,plain,(
% 1.47/0.54    ~v2_tex_2(sK1,sK0) | ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_tdlat_3(sK4(sK0,sK1))),
% 1.47/0.54    inference(resolution,[],[f218,f75])).
% 1.47/0.54  fof(f75,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_tdlat_3(X1)) )),
% 1.47/0.54    inference(subsumption_resolution,[],[f65,f56])).
% 1.47/0.54  fof(f65,plain,(
% 1.47/0.54    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v2_tdlat_3(X1)) )),
% 1.47/0.54    inference(cnf_transformation,[],[f34])).
% 1.47/0.54  fof(f34,plain,(
% 1.47/0.54    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.54    inference(flattening,[],[f33])).
% 1.47/0.54  fof(f33,plain,(
% 1.47/0.54    ! [X0] : (! [X1] : (v2_tdlat_3(X1) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.47/0.54    inference(ennf_transformation,[],[f10])).
% 1.47/0.54  fof(f10,axiom,(
% 1.47/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => v2_tdlat_3(X1)))),
% 1.47/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc6_tdlat_3)).
% 1.47/0.54  fof(f372,plain,(
% 1.47/0.54    ~v7_struct_0(sK4(sK0,sK1)) | ~l1_struct_0(sK4(sK0,sK1)) | v1_zfmisc_1(sK1)),
% 1.47/0.54    inference(superposition,[],[f72,f360])).
% 1.47/0.54  fof(f360,plain,(
% 1.47/0.54    sK1 = u1_struct_0(sK4(sK0,sK1))),
% 1.47/0.54    inference(global_subsumption,[],[f260,f285,f359])).
% 1.47/0.54  fof(f359,plain,(
% 1.47/0.54    ~m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK4(sK0,sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f358,f281])).
% 1.47/0.54  fof(f281,plain,(
% 1.47/0.54    ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK4(sK0,sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f280,f47])).
% 1.47/0.54  fof(f280,plain,(
% 1.47/0.54    v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK4(sK0,sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f279,f45])).
% 1.47/0.54  fof(f279,plain,(
% 1.47/0.54    v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK4(sK0,sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f278,f50])).
% 1.47/0.54  fof(f278,plain,(
% 1.47/0.54    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK4(sK0,sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f275,f48])).
% 1.47/0.54  fof(f275,plain,(
% 1.47/0.54    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK4(sK0,sK1))),
% 1.47/0.54    inference(resolution,[],[f71,f46])).
% 1.47/0.54  % (17121)Refutation not found, incomplete strategy% (17121)------------------------------
% 1.47/0.54  % (17121)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.54  % (17121)Termination reason: Refutation not found, incomplete strategy
% 1.47/0.54  
% 1.47/0.54  fof(f71,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_tex_2(X1,X0) | u1_struct_0(sK4(X0,X1)) = X1) )),
% 1.47/0.54    inference(cnf_transformation,[],[f38])).
% 1.47/0.54  % (17121)Memory used [KB]: 10618
% 1.47/0.54  fof(f358,plain,(
% 1.47/0.54    v2_tex_2(sK1,sK0) | ~m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | sK1 = u1_struct_0(sK4(sK0,sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f357,f47])).
% 1.47/0.54  % (17121)Time elapsed: 0.101 s
% 1.47/0.54  % (17121)------------------------------
% 1.47/0.54  % (17121)------------------------------
% 1.47/0.54  fof(f357,plain,(
% 1.47/0.54    v2_tex_2(sK1,sK0) | ~m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | sK1 = u1_struct_0(sK4(sK0,sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f356,f50])).
% 1.47/0.54  fof(f356,plain,(
% 1.47/0.54    v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | sK1 = u1_struct_0(sK4(sK0,sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f354,f48])).
% 1.47/0.54  fof(f354,plain,(
% 1.47/0.54    v2_tex_2(sK1,sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | sK1 = u1_struct_0(sK4(sK0,sK1))),
% 1.47/0.54    inference(superposition,[],[f66,f350])).
% 1.47/0.54  fof(f350,plain,(
% 1.47/0.54    sK1 = k6_domain_1(u1_struct_0(sK0),sK2(sK1)) | sK1 = u1_struct_0(sK4(sK0,sK1))),
% 1.47/0.54    inference(backward_demodulation,[],[f286,f346])).
% 1.47/0.54  fof(f346,plain,(
% 1.47/0.54    sK1 = k1_tarski(sK2(sK1))),
% 1.47/0.54    inference(duplicate_literal_removal,[],[f337])).
% 1.47/0.54  fof(f337,plain,(
% 1.47/0.54    sK1 = k1_tarski(sK2(sK1)) | sK1 = k1_tarski(sK2(sK1)) | sK1 = k1_tarski(sK2(sK1))),
% 1.47/0.54    inference(superposition,[],[f328,f329])).
% 1.47/0.54  fof(f329,plain,(
% 1.47/0.54    sK1 = k6_domain_1(sK1,sK2(sK1)) | sK1 = k1_tarski(sK2(sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f327,f45])).
% 1.47/0.54  fof(f327,plain,(
% 1.47/0.54    sK1 = k1_tarski(sK2(sK1)) | sK1 = k6_domain_1(sK1,sK2(sK1)) | v1_xboole_0(sK1)),
% 1.47/0.54    inference(resolution,[],[f324,f52])).
% 1.47/0.54  fof(f52,plain,(
% 1.47/0.54    ( ! [X0] : (~v1_zfmisc_1(X0) | k6_domain_1(X0,sK2(X0)) = X0 | v1_xboole_0(X0)) )),
% 1.47/0.54    inference(cnf_transformation,[],[f19])).
% 1.47/0.54  fof(f19,plain,(
% 1.47/0.54    ! [X0] : ((v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))) | v1_xboole_0(X0))),
% 1.47/0.54    inference(ennf_transformation,[],[f11])).
% 1.47/0.54  fof(f11,axiom,(
% 1.47/0.54    ! [X0] : (~v1_xboole_0(X0) => (v1_zfmisc_1(X0) <=> ? [X1] : (k6_domain_1(X0,X1) = X0 & m1_subset_1(X1,X0))))),
% 1.47/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tex_2)).
% 1.47/0.54  fof(f324,plain,(
% 1.47/0.54    v1_zfmisc_1(sK1) | sK1 = k1_tarski(sK2(sK1))),
% 1.47/0.54    inference(resolution,[],[f323,f43])).
% 1.47/0.54  fof(f43,plain,(
% 1.47/0.54    v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1)),
% 1.47/0.54    inference(cnf_transformation,[],[f18])).
% 1.47/0.54  fof(f323,plain,(
% 1.47/0.54    ~v2_tex_2(sK1,sK0) | sK1 = k1_tarski(sK2(sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f322,f234])).
% 1.47/0.54  fof(f322,plain,(
% 1.47/0.54    ~l1_struct_0(sK4(sK0,sK1)) | sK1 = k1_tarski(sK2(sK1)) | ~v2_tex_2(sK1,sK0)),
% 1.47/0.54    inference(subsumption_resolution,[],[f321,f44])).
% 1.47/0.54  fof(f321,plain,(
% 1.47/0.54    ~l1_struct_0(sK4(sK0,sK1)) | v1_zfmisc_1(sK1) | sK1 = k1_tarski(sK2(sK1)) | ~v2_tex_2(sK1,sK0)),
% 1.47/0.54    inference(resolution,[],[f311,f232])).
% 1.47/0.54  fof(f311,plain,(
% 1.47/0.54    ~v7_struct_0(sK4(sK0,sK1)) | ~l1_struct_0(sK4(sK0,sK1)) | v1_zfmisc_1(sK1) | sK1 = k1_tarski(sK2(sK1))),
% 1.47/0.54    inference(superposition,[],[f72,f299])).
% 1.47/0.54  fof(f299,plain,(
% 1.47/0.54    sK1 = u1_struct_0(sK4(sK0,sK1)) | sK1 = k1_tarski(sK2(sK1))),
% 1.47/0.54    inference(duplicate_literal_removal,[],[f294])).
% 1.47/0.54  fof(f294,plain,(
% 1.47/0.54    sK1 = k1_tarski(sK2(sK1)) | sK1 = u1_struct_0(sK4(sK0,sK1)) | sK1 = u1_struct_0(sK4(sK0,sK1))),
% 1.47/0.54    inference(superposition,[],[f289,f290])).
% 1.47/0.54  fof(f290,plain,(
% 1.47/0.54    sK1 = k6_domain_1(sK1,sK2(sK1)) | sK1 = u1_struct_0(sK4(sK0,sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f288,f45])).
% 1.47/0.54  fof(f288,plain,(
% 1.47/0.54    sK1 = u1_struct_0(sK4(sK0,sK1)) | sK1 = k6_domain_1(sK1,sK2(sK1)) | v1_xboole_0(sK1)),
% 1.47/0.54    inference(resolution,[],[f285,f52])).
% 1.47/0.54  fof(f289,plain,(
% 1.47/0.54    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) | sK1 = u1_struct_0(sK4(sK0,sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f287,f45])).
% 1.47/0.54  fof(f287,plain,(
% 1.47/0.54    sK1 = u1_struct_0(sK4(sK0,sK1)) | k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) | v1_xboole_0(sK1)),
% 1.47/0.54    inference(resolution,[],[f285,f88])).
% 1.47/0.54  fof(f88,plain,(
% 1.47/0.54    ( ! [X0] : (~v1_zfmisc_1(X0) | k6_domain_1(X0,sK2(X0)) = k1_tarski(sK2(X0)) | v1_xboole_0(X0)) )),
% 1.47/0.54    inference(duplicate_literal_removal,[],[f87])).
% 1.47/0.54  fof(f87,plain,(
% 1.47/0.54    ( ! [X0] : (v1_xboole_0(X0) | k6_domain_1(X0,sK2(X0)) = k1_tarski(sK2(X0)) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0)) )),
% 1.47/0.54    inference(resolution,[],[f73,f51])).
% 1.47/0.54  fof(f51,plain,(
% 1.47/0.54    ( ! [X0] : (m1_subset_1(sK2(X0),X0) | v1_xboole_0(X0) | ~v1_zfmisc_1(X0)) )),
% 1.47/0.54    inference(cnf_transformation,[],[f19])).
% 1.47/0.54  fof(f73,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,X0) | v1_xboole_0(X0) | k6_domain_1(X0,X1) = k1_tarski(X1)) )),
% 1.47/0.54    inference(cnf_transformation,[],[f42])).
% 1.47/0.54  fof(f42,plain,(
% 1.47/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | ~m1_subset_1(X1,X0) | v1_xboole_0(X0))),
% 1.47/0.54    inference(flattening,[],[f41])).
% 1.47/0.54  fof(f41,plain,(
% 1.47/0.54    ! [X0,X1] : (k6_domain_1(X0,X1) = k1_tarski(X1) | (~m1_subset_1(X1,X0) | v1_xboole_0(X0)))),
% 1.47/0.54    inference(ennf_transformation,[],[f6])).
% 1.47/0.54  fof(f6,axiom,(
% 1.47/0.54    ! [X0,X1] : ((m1_subset_1(X1,X0) & ~v1_xboole_0(X0)) => k6_domain_1(X0,X1) = k1_tarski(X1))),
% 1.47/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_domain_1)).
% 1.47/0.54  fof(f328,plain,(
% 1.47/0.54    k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) | sK1 = k1_tarski(sK2(sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f326,f45])).
% 1.47/0.54  fof(f326,plain,(
% 1.47/0.54    sK1 = k1_tarski(sK2(sK1)) | k6_domain_1(sK1,sK2(sK1)) = k1_tarski(sK2(sK1)) | v1_xboole_0(sK1)),
% 1.47/0.54    inference(resolution,[],[f324,f88])).
% 1.47/0.54  fof(f286,plain,(
% 1.47/0.54    sK1 = u1_struct_0(sK4(sK0,sK1)) | k6_domain_1(u1_struct_0(sK0),sK2(sK1)) = k1_tarski(sK2(sK1))),
% 1.47/0.54    inference(resolution,[],[f285,f169])).
% 1.47/0.54  fof(f169,plain,(
% 1.47/0.54    ~v1_zfmisc_1(sK1) | k6_domain_1(u1_struct_0(sK0),sK2(sK1)) = k1_tarski(sK2(sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f168,f45])).
% 1.47/0.54  fof(f168,plain,(
% 1.47/0.54    k6_domain_1(u1_struct_0(sK0),sK2(sK1)) = k1_tarski(sK2(sK1)) | v1_xboole_0(sK1) | ~v1_zfmisc_1(sK1)),
% 1.47/0.54    inference(resolution,[],[f167,f51])).
% 1.47/0.54  fof(f167,plain,(
% 1.47/0.54    ( ! [X2] : (~m1_subset_1(X2,sK1) | k6_domain_1(u1_struct_0(sK0),X2) = k1_tarski(X2)) )),
% 1.47/0.54    inference(subsumption_resolution,[],[f165,f81])).
% 1.47/0.54  fof(f81,plain,(
% 1.47/0.54    ~v1_xboole_0(u1_struct_0(sK0))),
% 1.47/0.54    inference(subsumption_resolution,[],[f79,f45])).
% 1.47/0.54  fof(f79,plain,(
% 1.47/0.54    ~v1_xboole_0(u1_struct_0(sK0)) | v1_xboole_0(sK1)),
% 1.47/0.54    inference(resolution,[],[f59,f46])).
% 1.47/0.54  fof(f59,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 1.47/0.54    inference(cnf_transformation,[],[f28])).
% 1.47/0.54  fof(f28,plain,(
% 1.47/0.54    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 1.47/0.54    inference(ennf_transformation,[],[f1])).
% 1.47/0.54  fof(f1,axiom,(
% 1.47/0.54    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 1.47/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_subset_1)).
% 1.47/0.54  fof(f165,plain,(
% 1.47/0.54    ( ! [X2] : (~m1_subset_1(X2,sK1) | v1_xboole_0(u1_struct_0(sK0)) | k6_domain_1(u1_struct_0(sK0),X2) = k1_tarski(X2)) )),
% 1.47/0.54    inference(resolution,[],[f163,f73])).
% 1.47/0.54  fof(f163,plain,(
% 1.47/0.54    ( ! [X0] : (m1_subset_1(X0,u1_struct_0(sK0)) | ~m1_subset_1(X0,sK1)) )),
% 1.47/0.54    inference(subsumption_resolution,[],[f162,f47])).
% 1.47/0.54  fof(f162,plain,(
% 1.47/0.54    ( ! [X0] : (~m1_subset_1(X0,sK1) | v2_struct_0(sK0) | m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.47/0.54    inference(subsumption_resolution,[],[f161,f50])).
% 1.47/0.54  fof(f161,plain,(
% 1.47/0.54    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,sK1) | v2_struct_0(sK0) | m1_subset_1(X0,u1_struct_0(sK0))) )),
% 1.47/0.54    inference(resolution,[],[f160,f104])).
% 1.47/0.54  fof(f104,plain,(
% 1.47/0.54    m1_pre_topc(sK3(sK0,sK1),sK0)),
% 1.47/0.54    inference(subsumption_resolution,[],[f103,f47])).
% 1.47/0.54  fof(f103,plain,(
% 1.47/0.54    v2_struct_0(sK0) | m1_pre_topc(sK3(sK0,sK1),sK0)),
% 1.47/0.54    inference(subsumption_resolution,[],[f102,f45])).
% 1.47/0.54  fof(f102,plain,(
% 1.47/0.54    v1_xboole_0(sK1) | v2_struct_0(sK0) | m1_pre_topc(sK3(sK0,sK1),sK0)),
% 1.47/0.54    inference(subsumption_resolution,[],[f100,f50])).
% 1.47/0.54  fof(f100,plain,(
% 1.47/0.54    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | m1_pre_topc(sK3(sK0,sK1),sK0)),
% 1.47/0.54    inference(resolution,[],[f62,f46])).
% 1.47/0.54  fof(f62,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | m1_pre_topc(sK3(X0,X1),X0)) )),
% 1.47/0.54    inference(cnf_transformation,[],[f30])).
% 1.47/0.54  fof(f30,plain,(
% 1.47/0.54    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.47/0.54    inference(flattening,[],[f29])).
% 1.47/0.54  fof(f29,plain,(
% 1.47/0.54    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.47/0.54    inference(ennf_transformation,[],[f12])).
% 1.47/0.54  fof(f12,axiom,(
% 1.47/0.54    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 1.47/0.54    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).
% 1.47/0.54  fof(f160,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~m1_pre_topc(sK3(sK0,sK1),X1) | ~l1_pre_topc(X1) | ~m1_subset_1(X0,sK1) | v2_struct_0(X1) | m1_subset_1(X0,u1_struct_0(X1))) )),
% 1.47/0.54    inference(subsumption_resolution,[],[f159,f94])).
% 1.47/0.54  fof(f94,plain,(
% 1.47/0.54    ~v2_struct_0(sK3(sK0,sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f93,f47])).
% 1.47/0.54  fof(f93,plain,(
% 1.47/0.54    v2_struct_0(sK0) | ~v2_struct_0(sK3(sK0,sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f92,f45])).
% 1.47/0.54  fof(f92,plain,(
% 1.47/0.54    v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_struct_0(sK3(sK0,sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f90,f50])).
% 1.47/0.54  fof(f90,plain,(
% 1.47/0.54    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v2_struct_0(sK3(sK0,sK1))),
% 1.47/0.54    inference(resolution,[],[f60,f46])).
% 1.47/0.54  fof(f60,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v2_struct_0(sK3(X0,X1))) )),
% 1.47/0.54    inference(cnf_transformation,[],[f30])).
% 1.47/0.54  fof(f159,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~m1_subset_1(X0,sK1) | ~l1_pre_topc(X1) | v2_struct_0(sK3(sK0,sK1)) | ~m1_pre_topc(sK3(sK0,sK1),X1) | v2_struct_0(X1) | m1_subset_1(X0,u1_struct_0(X1))) )),
% 1.47/0.54    inference(superposition,[],[f64,f123])).
% 1.47/0.54  fof(f123,plain,(
% 1.47/0.54    sK1 = u1_struct_0(sK3(sK0,sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f122,f47])).
% 1.47/0.54  fof(f122,plain,(
% 1.47/0.54    v2_struct_0(sK0) | sK1 = u1_struct_0(sK3(sK0,sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f121,f45])).
% 1.47/0.54  fof(f121,plain,(
% 1.47/0.54    v1_xboole_0(sK1) | v2_struct_0(sK0) | sK1 = u1_struct_0(sK3(sK0,sK1))),
% 1.47/0.54    inference(subsumption_resolution,[],[f119,f50])).
% 1.47/0.54  fof(f119,plain,(
% 1.47/0.54    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | sK1 = u1_struct_0(sK3(sK0,sK1))),
% 1.47/0.54    inference(resolution,[],[f63,f46])).
% 1.47/0.54  fof(f63,plain,(
% 1.47/0.54    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | u1_struct_0(sK3(X0,X1)) = X1) )),
% 1.47/0.54    inference(cnf_transformation,[],[f30])).
% 1.47/0.55  % (17123)dis-10_1_aac=none:afr=on:afp=10000:afq=1.0:amm=off:anc=none:fsr=off:gs=on:gsem=off:irw=on:nm=4:newcnf=on:nwc=2:sp=occurrence_2 on theBenchmark
% 1.60/0.56  % (17128)Refutation not found, incomplete strategy% (17128)------------------------------
% 1.60/0.56  % (17128)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.56  % (17128)Termination reason: Refutation not found, incomplete strategy
% 1.60/0.56  
% 1.60/0.56  % (17128)Memory used [KB]: 1791
% 1.60/0.56  % (17128)Time elapsed: 0.136 s
% 1.60/0.56  % (17128)------------------------------
% 1.60/0.56  % (17128)------------------------------
% 1.60/0.56  fof(f64,plain,(
% 1.60/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,u1_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | m1_subset_1(X2,u1_struct_0(X0))) )),
% 1.60/0.56    inference(cnf_transformation,[],[f32])).
% 1.60/0.56  fof(f32,plain,(
% 1.60/0.56    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 1.60/0.56    inference(flattening,[],[f31])).
% 1.60/0.56  fof(f31,plain,(
% 1.60/0.56    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,u1_struct_0(X0)) | ~m1_subset_1(X2,u1_struct_0(X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 1.60/0.56    inference(ennf_transformation,[],[f5])).
% 1.60/0.56  fof(f5,axiom,(
% 1.60/0.56    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ! [X2] : (m1_subset_1(X2,u1_struct_0(X1)) => m1_subset_1(X2,u1_struct_0(X0)))))),
% 1.60/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_pre_topc)).
% 1.60/0.56  fof(f66,plain,(
% 1.60/0.56    ( ! [X0,X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,u1_struct_0(X0)) | v2_struct_0(X0)) )),
% 1.60/0.56    inference(cnf_transformation,[],[f36])).
% 1.60/0.56  fof(f36,plain,(
% 1.60/0.56    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.60/0.56    inference(flattening,[],[f35])).
% 1.60/0.56  fof(f35,plain,(
% 1.60/0.56    ! [X0] : (! [X1] : (v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,u1_struct_0(X0))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.60/0.56    inference(ennf_transformation,[],[f14])).
% 1.60/0.56  fof(f14,axiom,(
% 1.60/0.56    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,u1_struct_0(X0)) => v2_tex_2(k6_domain_1(u1_struct_0(X0),X1),X0)))),
% 1.60/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_tex_2)).
% 1.60/0.56  fof(f285,plain,(
% 1.60/0.56    v1_zfmisc_1(sK1) | sK1 = u1_struct_0(sK4(sK0,sK1))),
% 1.60/0.56    inference(resolution,[],[f281,f43])).
% 1.60/0.56  fof(f72,plain,(
% 1.60/0.56    ( ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0)) )),
% 1.60/0.56    inference(cnf_transformation,[],[f40])).
% 1.60/0.56  fof(f40,plain,(
% 1.60/0.56    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | ~l1_struct_0(X0) | ~v7_struct_0(X0))),
% 1.60/0.56    inference(flattening,[],[f39])).
% 1.60/0.56  fof(f39,plain,(
% 1.60/0.56    ! [X0] : (v1_zfmisc_1(u1_struct_0(X0)) | (~l1_struct_0(X0) | ~v7_struct_0(X0)))),
% 1.60/0.56    inference(ennf_transformation,[],[f4])).
% 1.60/0.56  fof(f4,axiom,(
% 1.60/0.56    ! [X0] : ((l1_struct_0(X0) & v7_struct_0(X0)) => v1_zfmisc_1(u1_struct_0(X0)))),
% 1.60/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_struct_0)).
% 1.60/0.56  fof(f395,plain,(
% 1.60/0.56    v2_tex_2(sK1,sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0)),
% 1.60/0.56    inference(superposition,[],[f66,f387])).
% 1.60/0.56  fof(f387,plain,(
% 1.60/0.56    sK1 = k6_domain_1(u1_struct_0(sK0),sK2(sK1))),
% 1.60/0.56    inference(resolution,[],[f386,f347])).
% 1.60/0.56  fof(f347,plain,(
% 1.60/0.56    ~v1_zfmisc_1(sK1) | sK1 = k6_domain_1(u1_struct_0(sK0),sK2(sK1))),
% 1.60/0.56    inference(backward_demodulation,[],[f169,f346])).
% 1.60/0.56  fof(f386,plain,(
% 1.60/0.56    v1_zfmisc_1(sK1)),
% 1.60/0.56    inference(resolution,[],[f385,f43])).
% 1.60/0.56  fof(f260,plain,(
% 1.60/0.56    m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | ~v1_zfmisc_1(sK1)),
% 1.60/0.56    inference(subsumption_resolution,[],[f259,f50])).
% 1.60/0.56  fof(f259,plain,(
% 1.60/0.56    m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~v1_zfmisc_1(sK1)),
% 1.60/0.56    inference(subsumption_resolution,[],[f258,f47])).
% 1.60/0.56  fof(f258,plain,(
% 1.60/0.56    m1_subset_1(sK2(sK1),u1_struct_0(sK0)) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v1_zfmisc_1(sK1)),
% 1.60/0.56    inference(resolution,[],[f255,f104])).
% 1.60/0.56  fof(f255,plain,(
% 1.60/0.56    ( ! [X0] : (~m1_pre_topc(sK3(sK0,sK1),X0) | m1_subset_1(sK2(sK1),u1_struct_0(X0)) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~v1_zfmisc_1(sK1)) )),
% 1.60/0.56    inference(subsumption_resolution,[],[f254,f45])).
% 1.60/0.56  fof(f254,plain,(
% 1.60/0.56    ( ! [X0] : (m1_subset_1(sK2(sK1),u1_struct_0(X0)) | ~m1_pre_topc(sK3(sK0,sK1),X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(sK1) | ~v1_zfmisc_1(sK1)) )),
% 1.60/0.56    inference(subsumption_resolution,[],[f250,f94])).
% 1.60/0.56  fof(f250,plain,(
% 1.60/0.56    ( ! [X0] : (m1_subset_1(sK2(sK1),u1_struct_0(X0)) | v2_struct_0(sK3(sK0,sK1)) | ~m1_pre_topc(sK3(sK0,sK1),X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(sK1) | ~v1_zfmisc_1(sK1)) )),
% 1.60/0.56    inference(superposition,[],[f158,f123])).
% 1.60/0.56  fof(f158,plain,(
% 1.60/0.56    ( ! [X0,X1] : (m1_subset_1(sK2(u1_struct_0(X1)),u1_struct_0(X0)) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(u1_struct_0(X1)) | ~v1_zfmisc_1(u1_struct_0(X1))) )),
% 1.60/0.56    inference(resolution,[],[f64,f51])).
% 1.60/0.56  % SZS output end Proof for theBenchmark
% 1.60/0.56  % (17124)------------------------------
% 1.60/0.56  % (17124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.60/0.56  % (17124)Termination reason: Refutation
% 1.60/0.56  
% 1.60/0.56  % (17124)Memory used [KB]: 6524
% 1.60/0.56  % (17124)Time elapsed: 0.134 s
% 1.60/0.56  % (17124)------------------------------
% 1.60/0.56  % (17124)------------------------------
% 1.60/0.57  % (17109)Success in time 0.203 s
%------------------------------------------------------------------------------
