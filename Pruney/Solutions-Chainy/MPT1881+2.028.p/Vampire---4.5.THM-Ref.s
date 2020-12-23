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
% DateTime   : Thu Dec  3 13:21:56 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 622 expanded)
%              Number of leaves         :   11 ( 113 expanded)
%              Depth                    :   18
%              Number of atoms          :  335 (3025 expanded)
%              Number of equality atoms :   28 (  88 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f162,plain,(
    $false ),
    inference(subsumption_resolution,[],[f159,f150])).

fof(f150,plain,(
    v1_subset_1(sK1,sK1) ),
    inference(subsumption_resolution,[],[f133,f148])).

fof(f148,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f88,f131])).

fof(f131,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f127,f130])).

fof(f130,plain,(
    sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f128,f126])).

fof(f126,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | sK1 = u1_struct_0(sK0) ),
    inference(backward_demodulation,[],[f73,f124])).

fof(f124,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f69,f122])).

fof(f122,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f121,f37])).

fof(f37,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).

fof(f121,plain,
    ( ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f120,f33])).

fof(f33,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f120,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f117,f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v4_pre_topc(X1,X0)
          <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).

fof(f117,plain,(
    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f116,f36])).

fof(f36,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f116,plain,
    ( v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v1_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f97,f37])).

fof(f97,plain,
    ( ~ l1_pre_topc(sK0)
    | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)
    | ~ v1_tdlat_3(sK0) ),
    inference(resolution,[],[f58,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(X1,X0)
      | ~ v1_tdlat_3(X0) ) ),
    inference(subsumption_resolution,[],[f48,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0)
      | ~ v1_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f58,plain,(
    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f51,f33])).

fof(f51,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).

fof(f69,plain,
    ( ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f68,f37])).

fof(f68,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v4_pre_topc(sK1,sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f40,f33])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f73,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f72,f37])).

fof(f72,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f42,f33])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(f128,plain,
    ( sK1 = u1_struct_0(sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f119,f83])).

fof(f83,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f82,f63])).

fof(f63,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f62,f36])).

fof(f62,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v1_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f61,f37])).

fof(f61,plain,
    ( ~ l1_pre_topc(sK0)
    | v3_pre_topc(sK1,sK0)
    | ~ v1_tdlat_3(sK0) ),
    inference(resolution,[],[f56,f33])).

fof(f82,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f81,f34])).

fof(f34,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f81,plain,
    ( v2_struct_0(sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f80,f37])).

fof(f80,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f79,f35])).

fof(f35,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f79,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f46,f33])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).

fof(f119,plain,
    ( v3_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f59,f31])).

fof(f31,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f59,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f52,f33])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f127,plain,
    ( sK1 != u1_struct_0(sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f71,f124])).

fof(f71,plain,
    ( u1_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f70,f37])).

fof(f70,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f41,f33])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f88,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f87,f67])).

fof(f67,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f66,f34])).

fof(f66,plain,
    ( v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f65,f37])).

fof(f65,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f64,f36])).

fof(f64,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f55,f33])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(subsumption_resolution,[],[f45,f38])).

fof(f45,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

fof(f87,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f86,f34])).

fof(f86,plain,
    ( v2_struct_0(sK0)
    | ~ v1_tops_1(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f85,f37])).

fof(f85,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_tops_1(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f84,f35])).

fof(f84,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | ~ v1_tops_1(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f47,f33])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ v1_tops_1(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).

fof(f133,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(backward_demodulation,[],[f32,f130])).

fof(f32,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f14])).

fof(f159,plain,(
    ~ v1_subset_1(sK1,sK1) ),
    inference(resolution,[],[f134,f54])).

fof(f54,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f134,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f33,f130])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 09:37:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (22552)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.46  % (22546)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.46  % (22543)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.46  % (22552)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.47  % (22541)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f162,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(subsumption_resolution,[],[f159,f150])).
% 0.20/0.47  fof(f150,plain,(
% 0.20/0.47    v1_subset_1(sK1,sK1)),
% 0.20/0.47    inference(subsumption_resolution,[],[f133,f148])).
% 0.20/0.47  fof(f148,plain,(
% 0.20/0.47    v3_tex_2(sK1,sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f88,f131])).
% 0.20/0.47  fof(f131,plain,(
% 0.20/0.47    v1_tops_1(sK1,sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f127,f130])).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    sK1 = u1_struct_0(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f128,f126])).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    ~v1_tops_1(sK1,sK0) | sK1 = u1_struct_0(sK0)),
% 0.20/0.47    inference(backward_demodulation,[],[f73,f124])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    sK1 = k2_pre_topc(sK0,sK1)),
% 0.20/0.47    inference(subsumption_resolution,[],[f69,f122])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    v4_pre_topc(sK1,sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f121,f37])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    l1_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  fof(f12,negated_conjecture,(
% 0.20/0.47    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.20/0.47    inference(negated_conjecture,[],[f11])).
% 0.20/0.47  fof(f11,conjecture,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | v4_pre_topc(sK1,sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f120,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v4_pre_topc(sK1,sK0)),
% 0.20/0.47    inference(resolution,[],[f117,f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v4_pre_topc(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) <=> v3_pre_topc(k3_subset_1(u1_struct_0(X0),X1),X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_tops_1)).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f116,f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    v1_tdlat_3(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v1_tdlat_3(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f97,f37])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | v3_pre_topc(k3_subset_1(u1_struct_0(sK0),sK1),sK0) | ~v1_tdlat_3(sK0)),
% 0.20/0.47    inference(resolution,[],[f58,f56])).
% 0.20/0.47  fof(f56,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v3_pre_topc(X1,X0) | ~v1_tdlat_3(X0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f48,f38])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_pre_topc(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_tdlat_3)).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X1,X0) | ~v1_tdlat_3(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    m1_subset_1(k3_subset_1(u1_struct_0(sK0),sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    inference(resolution,[],[f51,f33])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => m1_subset_1(k3_subset_1(X0,X1),k1_zfmisc_1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_subset_1)).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.20/0.47    inference(subsumption_resolution,[],[f68,f37])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | ~v4_pre_topc(sK1,sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.20/0.47    inference(resolution,[],[f40,f33])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    ~v1_tops_1(sK1,sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.20/0.47    inference(subsumption_resolution,[],[f72,f37])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~v1_tops_1(sK1,sK0)),
% 0.20/0.47    inference(resolution,[],[f42,f33])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    sK1 = u1_struct_0(sK0) | v1_tops_1(sK1,sK0)),
% 0.20/0.47    inference(resolution,[],[f119,f83])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    ~v3_tex_2(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f82,f63])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    v3_pre_topc(sK1,sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f62,f36])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    v3_pre_topc(sK1,sK0) | ~v1_tdlat_3(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f61,f37])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | v3_pre_topc(sK1,sK0) | ~v1_tdlat_3(sK0)),
% 0.20/0.47    inference(resolution,[],[f56,f33])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    ~v3_pre_topc(sK1,sK0) | ~v3_tex_2(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f81,f34])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    ~v2_struct_0(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    v2_struct_0(sK0) | ~v3_pre_topc(sK1,sK0) | ~v3_tex_2(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f80,f37])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_pre_topc(sK1,sK0) | ~v3_tex_2(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f79,f35])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    v2_pre_topc(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v3_pre_topc(sK1,sK0) | ~v3_tex_2(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 0.20/0.47    inference(resolution,[],[f46,f33])).
% 0.20/0.47  fof(f46,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v3_pre_topc(X1,X0) | ~v3_tex_2(X1,X0) | v1_tops_1(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    v3_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK0)),
% 0.20/0.47    inference(resolution,[],[f59,f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f59,plain,(
% 0.20/0.47    v1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)),
% 0.20/0.47    inference(resolution,[],[f52,f33])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    sK1 != u1_struct_0(sK0) | v1_tops_1(sK1,sK0)),
% 0.20/0.47    inference(backward_demodulation,[],[f71,f124])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    u1_struct_0(sK0) != k2_pre_topc(sK0,sK1) | v1_tops_1(sK1,sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f70,f37])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | u1_struct_0(sK0) != k2_pre_topc(sK0,sK1) | v1_tops_1(sK1,sK0)),
% 0.20/0.47    inference(resolution,[],[f41,f33])).
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | u1_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    ~v1_tops_1(sK1,sK0) | v3_tex_2(sK1,sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f87,f67])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    v2_tex_2(sK1,sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f66,f34])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    v2_struct_0(sK0) | v2_tex_2(sK1,sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f65,f37])).
% 0.20/0.47  fof(f65,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_tex_2(sK1,sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f64,f36])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_tex_2(sK1,sK0)),
% 0.20/0.47    inference(resolution,[],[f55,f33])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_tex_2(X1,X0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f45,f38])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    ~v1_tops_1(sK1,sK0) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f86,f34])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    v2_struct_0(sK0) | ~v1_tops_1(sK1,sK0) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f85,f37])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v1_tops_1(sK1,sK0) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f84,f35])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | ~v1_tops_1(sK1,sK0) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0)),
% 0.20/0.47    inference(resolution,[],[f47,f33])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | ~v1_tops_1(X1,X0) | ~v2_tex_2(X1,X0) | v3_tex_2(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).
% 0.20/0.47  fof(f133,plain,(
% 0.20/0.47    v1_subset_1(sK1,sK1) | ~v3_tex_2(sK1,sK0)),
% 0.20/0.47    inference(backward_demodulation,[],[f32,f130])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ~v3_tex_2(sK1,sK0) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f159,plain,(
% 0.20/0.47    ~v1_subset_1(sK1,sK1)),
% 0.20/0.47    inference(resolution,[],[f134,f54])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 0.20/0.47    inference(equality_resolution,[],[f53])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f30])).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.20/0.47    inference(backward_demodulation,[],[f33,f130])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (22552)------------------------------
% 0.20/0.47  % (22552)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (22552)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (22552)Memory used [KB]: 1663
% 0.20/0.47  % (22552)Time elapsed: 0.050 s
% 0.20/0.47  % (22552)------------------------------
% 0.20/0.47  % (22552)------------------------------
% 0.20/0.47  % (22534)Success in time 0.117 s
%------------------------------------------------------------------------------
