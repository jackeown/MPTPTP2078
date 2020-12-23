%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:17 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  135 (10009 expanded)
%              Number of leaves         :   13 (1725 expanded)
%              Depth                    :   44
%              Number of atoms          :  499 (63899 expanded)
%              Number of equality atoms :   43 (1008 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    6 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f306,plain,(
    $false ),
    inference(subsumption_resolution,[],[f305,f94])).

fof(f94,plain,(
    ~ v1_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f93,f42])).

fof(f42,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( v1_subset_1(X1,u1_struct_0(X0))
          & v3_tex_2(X1,X0)
          & ( v4_pre_topc(X1,X0)
            | v3_pre_topc(X1,X0) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v3_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v3_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ~ ( v1_subset_1(X1,u1_struct_0(X0))
                & v3_tex_2(X1,X0)
                & ( v4_pre_topc(X1,X0)
                  | v3_pre_topc(X1,X0) ) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v3_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ~ ( v1_subset_1(X1,u1_struct_0(X0))
              & v3_tex_2(X1,X0)
              & ( v4_pre_topc(X1,X0)
                | v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tex_2)).

fof(f93,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f92,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f92,plain,
    ( ~ v1_tdlat_3(sK0)
    | v2_struct_0(sK0)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f91,f41])).

fof(f41,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f91,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f90,f47])).

fof(f47,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f90,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f89,f45])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f89,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f43,f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,u1_struct_0(X0))
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f43,plain,(
    v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f18])).

fof(f305,plain,(
    v1_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f304,f45])).

fof(f304,plain,
    ( ~ v2_pre_topc(sK0)
    | v1_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f301,f47])).

fof(f301,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | v1_tdlat_3(sK0) ),
    inference(resolution,[],[f276,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(sK5(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v1_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f276,plain,(
    v3_pre_topc(sK5(sK0),sK0) ),
    inference(subsumption_resolution,[],[f275,f162])).

fof(f162,plain,(
    m1_subset_1(sK5(sK0),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f156,f94])).

fof(f156,plain,
    ( m1_subset_1(sK5(sK0),k1_zfmisc_1(sK1))
    | v1_tdlat_3(sK0) ),
    inference(backward_demodulation,[],[f85,f153])).

fof(f153,plain,(
    sK1 = u1_struct_0(sK0) ),
    inference(forward_demodulation,[],[f152,f133])).

fof(f133,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f132,f47])).

fof(f132,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f130,f41])).

fof(f130,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f129,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f129,plain,(
    v4_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f128,f46])).

fof(f46,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f128,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f127,f45])).

fof(f127,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f126,f41])).

fof(f126,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f125,f47])).

fof(f125,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(duplicate_literal_removal,[],[f123])).

fof(f123,plain,
    ( v4_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v4_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(resolution,[],[f40,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(X1,X0)
      | ~ v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v4_pre_topc(X1,X0)
            | ~ v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
             => v4_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tdlat_3)).

fof(f40,plain,
    ( v3_pre_topc(sK1,sK0)
    | v4_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f152,plain,(
    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f151,f47])).

fof(f151,plain,
    ( u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f150,f41])).

fof(f150,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f149,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ v1_tops_1(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(f149,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f148,f42])).

fof(f148,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f147,f44])).

fof(f147,plain,
    ( v2_struct_0(sK0)
    | ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f146,f41])).

fof(f146,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f145,f47])).

fof(f145,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f144,f45])).

fof(f144,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ v3_tex_2(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f142,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | ~ v3_tex_2(X1,X0)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).

fof(f142,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f141,f46])).

fof(f141,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f140,f45])).

fof(f140,plain,
    ( ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f139,f41])).

fof(f139,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f131,f47])).

fof(f131,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(sK1,sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(resolution,[],[f129,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v4_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | v3_pre_topc(X1,X0)
      | ~ v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ v4_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v4_pre_topc(X1,X0)
             => v3_pre_topc(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).

fof(f85,plain,
    ( m1_subset_1(sK5(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f80,f47])).

fof(f80,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(sK5(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tdlat_3(sK0) ),
    inference(resolution,[],[f45,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v1_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f275,plain,
    ( ~ m1_subset_1(sK5(sK0),k1_zfmisc_1(sK1))
    | v3_pre_topc(sK5(sK0),sK0) ),
    inference(forward_demodulation,[],[f266,f264])).

fof(f264,plain,(
    sK5(sK0) = k2_pre_topc(sK0,sK5(sK0)) ),
    inference(forward_demodulation,[],[f256,f208])).

fof(f208,plain,(
    sK5(sK0) = k9_subset_1(sK1,sK1,k2_pre_topc(sK0,sK5(sK0))) ),
    inference(resolution,[],[f164,f162])).

fof(f164,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | k9_subset_1(sK1,sK1,k2_pre_topc(sK0,X0)) = X0 ) ),
    inference(forward_demodulation,[],[f163,f153])).

fof(f163,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f158,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f158,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(sK1))
      | ~ r1_tarski(X0,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 ) ),
    inference(backward_demodulation,[],[f120,f153])).

fof(f120,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 ) ),
    inference(subsumption_resolution,[],[f119,f44])).

fof(f119,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f118,f41])).

fof(f118,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f117,f47])).

fof(f117,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0
      | v2_struct_0(sK0) ) ),
    inference(subsumption_resolution,[],[f111,f45])).

fof(f111,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,sK1)
      | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0
      | v2_struct_0(sK0) ) ),
    inference(resolution,[],[f88,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r1_tarski(X2,X1)
      | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2
                | ~ r1_tarski(X2,X1)
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v2_tex_2(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( r1_tarski(X2,X1)
                 => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).

fof(f88,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f87,f47])).

fof(f87,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f86,f41])).

fof(f86,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f42,f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( X1 = X2
                  | ~ r1_tarski(X1,X2)
                  | ~ v2_tex_2(X2,X0)
                  | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
              & v2_tex_2(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ( ! [X2] :
                  ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( r1_tarski(X1,X2)
                      & v2_tex_2(X2,X0) )
                   => X1 = X2 ) )
              & v2_tex_2(X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f256,plain,(
    k2_pre_topc(sK0,sK5(sK0)) = k9_subset_1(sK1,sK1,k2_pre_topc(sK0,sK5(sK0))) ),
    inference(backward_demodulation,[],[f214,f254])).

fof(f254,plain,(
    k2_pre_topc(sK0,sK5(sK0)) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))) ),
    inference(forward_demodulation,[],[f253,f214])).

fof(f253,plain,(
    k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))) = k9_subset_1(sK1,sK1,k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0)))) ),
    inference(forward_demodulation,[],[f248,f225])).

fof(f225,plain,(
    k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0)))) ),
    inference(subsumption_resolution,[],[f224,f213])).

fof(f213,plain,(
    m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f211,f192])).

fof(f192,plain,(
    ! [X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(sK1))
      | m1_subset_1(k2_pre_topc(sK0,X9),k1_zfmisc_1(sK1)) ) ),
    inference(subsumption_resolution,[],[f177,f47])).

fof(f177,plain,(
    ! [X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(sK1))
      | ~ l1_pre_topc(sK0)
      | m1_subset_1(k2_pre_topc(sK0,X9),k1_zfmisc_1(sK1)) ) ),
    inference(superposition,[],[f79,f153])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f211,plain,(
    m1_subset_1(k2_pre_topc(sK0,sK5(sK0)),k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f192,f162])).

fof(f224,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))),k1_zfmisc_1(sK1))
    | k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0)))) ),
    inference(forward_demodulation,[],[f223,f153])).

fof(f223,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0)))) ),
    inference(subsumption_resolution,[],[f221,f47])).

fof(f221,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0)))) ),
    inference(resolution,[],[f215,f67])).

fof(f215,plain,(
    v4_pre_topc(k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))),sK0) ),
    inference(resolution,[],[f211,f179])).

fof(f179,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
      | v4_pre_topc(k2_pre_topc(sK0,X2),sK0) ) ),
    inference(subsumption_resolution,[],[f178,f45])).

fof(f178,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
      | ~ v2_pre_topc(sK0)
      | v4_pre_topc(k2_pre_topc(sK0,X2),sK0) ) ),
    inference(subsumption_resolution,[],[f170,f47])).

fof(f170,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(sK0)
      | v4_pre_topc(k2_pre_topc(sK0,X2),sK0) ) ),
    inference(superposition,[],[f57,f153])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( v4_pre_topc(k2_pre_topc(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_pre_topc(X0,X1),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).

fof(f248,plain,(
    k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))) = k9_subset_1(sK1,sK1,k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))))) ),
    inference(resolution,[],[f213,f164])).

fof(f214,plain,(
    k2_pre_topc(sK0,sK5(sK0)) = k9_subset_1(sK1,sK1,k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0)))) ),
    inference(resolution,[],[f211,f164])).

fof(f266,plain,
    ( v3_pre_topc(sK5(sK0),sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK5(sK0)),k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f206,f264])).

fof(f206,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK5(sK0)),k1_zfmisc_1(sK1))
    | v3_pre_topc(k2_pre_topc(sK0,sK5(sK0)),sK0) ),
    inference(forward_demodulation,[],[f205,f153])).

fof(f205,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK5(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k2_pre_topc(sK0,sK5(sK0)),sK0) ),
    inference(subsumption_resolution,[],[f204,f46])).

fof(f204,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK5(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k2_pre_topc(sK0,sK5(sK0)),sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f203,f45])).

fof(f203,plain,
    ( ~ m1_subset_1(k2_pre_topc(sK0,sK5(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(k2_pre_topc(sK0,sK5(sK0)),sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f200,f47])).

fof(f200,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(k2_pre_topc(sK0,sK5(sK0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | v3_pre_topc(k2_pre_topc(sK0,sK5(sK0)),sK0)
    | ~ v3_tdlat_3(sK0) ),
    inference(resolution,[],[f196,f58])).

fof(f196,plain,(
    v4_pre_topc(k2_pre_topc(sK0,sK5(sK0)),sK0) ),
    inference(resolution,[],[f179,f162])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:59:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (20601)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.46  % (20601)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (20617)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f306,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(subsumption_resolution,[],[f305,f94])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    ~v1_tdlat_3(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f93,f42])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    v3_tex_2(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : ((v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,negated_conjecture,(
% 0.21/0.47    ~! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 0.21/0.47    inference(negated_conjecture,[],[f15])).
% 0.21/0.47  fof(f15,conjecture,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v3_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ~(v1_subset_1(X1,u1_struct_0(X0)) & v3_tex_2(X1,X0) & (v4_pre_topc(X1,X0) | v3_pre_topc(X1,X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_tex_2)).
% 0.21/0.47  fof(f93,plain,(
% 0.21/0.47    ~v1_tdlat_3(sK0) | ~v3_tex_2(sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f92,f44])).
% 0.21/0.47  fof(f44,plain,(
% 0.21/0.47    ~v2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f92,plain,(
% 0.21/0.47    ~v1_tdlat_3(sK0) | v2_struct_0(sK0) | ~v3_tex_2(sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f91,f41])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    ~v1_tdlat_3(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~v3_tex_2(sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f90,f47])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    l1_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f90,plain,(
% 0.21/0.47    ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~v3_tex_2(sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f89,f45])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    v2_pre_topc(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f89,plain,(
% 0.21/0.47    ~v2_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~v3_tex_2(sK1,sK0)),
% 0.21/0.47    inference(resolution,[],[f43,f49])).
% 0.21/0.47  fof(f49,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_subset_1(X1,u1_struct_0(X0)) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | ~v3_tex_2(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).
% 0.21/0.47  fof(f43,plain,(
% 0.21/0.47    v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f305,plain,(
% 0.21/0.47    v1_tdlat_3(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f304,f45])).
% 0.21/0.47  fof(f304,plain,(
% 0.21/0.47    ~v2_pre_topc(sK0) | v1_tdlat_3(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f301,f47])).
% 0.21/0.47  fof(f301,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v1_tdlat_3(sK0)),
% 0.21/0.47    inference(resolution,[],[f276,f70])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    ( ! [X0] : (~v3_pre_topc(sK5(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v1_tdlat_3(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f34])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f33])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).
% 0.21/0.47  fof(f276,plain,(
% 0.21/0.47    v3_pre_topc(sK5(sK0),sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f275,f162])).
% 0.21/0.47  fof(f162,plain,(
% 0.21/0.47    m1_subset_1(sK5(sK0),k1_zfmisc_1(sK1))),
% 0.21/0.47    inference(subsumption_resolution,[],[f156,f94])).
% 0.21/0.47  fof(f156,plain,(
% 0.21/0.47    m1_subset_1(sK5(sK0),k1_zfmisc_1(sK1)) | v1_tdlat_3(sK0)),
% 0.21/0.47    inference(backward_demodulation,[],[f85,f153])).
% 0.21/0.47  fof(f153,plain,(
% 0.21/0.47    sK1 = u1_struct_0(sK0)),
% 0.21/0.47    inference(forward_demodulation,[],[f152,f133])).
% 0.21/0.47  fof(f133,plain,(
% 0.21/0.47    sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f132,f47])).
% 0.21/0.47  fof(f132,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f130,f41])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.21/0.47    inference(resolution,[],[f129,f67])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | k2_pre_topc(X0,X1) = X1) )),
% 0.21/0.47    inference(cnf_transformation,[],[f32])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f31])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.47  fof(f129,plain,(
% 0.21/0.47    v4_pre_topc(sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f128,f46])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    v3_tdlat_3(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f128,plain,(
% 0.21/0.47    v4_pre_topc(sK1,sK0) | ~v3_tdlat_3(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f127,f45])).
% 0.21/0.47  fof(f127,plain,(
% 0.21/0.47    v4_pre_topc(sK1,sK0) | ~v2_pre_topc(sK0) | ~v3_tdlat_3(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f126,f41])).
% 0.21/0.47  fof(f126,plain,(
% 0.21/0.47    v4_pre_topc(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~v3_tdlat_3(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f125,f47])).
% 0.21/0.47  fof(f125,plain,(
% 0.21/0.47    v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~v3_tdlat_3(sK0)),
% 0.21/0.47    inference(duplicate_literal_removal,[],[f123])).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    v4_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v4_pre_topc(sK1,sK0) | ~v3_tdlat_3(sK0)),
% 0.21/0.47    inference(resolution,[],[f40,f62])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v3_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | v4_pre_topc(X1,X0) | ~v3_tdlat_3(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f30])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v4_pre_topc(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f29])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v4_pre_topc(X1,X0) | ~v3_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) => v4_pre_topc(X1,X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t23_tdlat_3)).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    v3_pre_topc(sK1,sK0) | v4_pre_topc(sK1,sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f152,plain,(
% 0.21/0.47    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.21/0.47    inference(subsumption_resolution,[],[f151,f47])).
% 0.21/0.47  fof(f151,plain,(
% 0.21/0.47    u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f150,f41])).
% 0.21/0.47  fof(f150,plain,(
% 0.21/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) | ~l1_pre_topc(sK0)),
% 0.21/0.47    inference(resolution,[],[f149,f72])).
% 0.21/0.47  fof(f72,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f35])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).
% 0.21/0.47  fof(f149,plain,(
% 0.21/0.47    v1_tops_1(sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f148,f42])).
% 0.21/0.47  fof(f148,plain,(
% 0.21/0.47    ~v3_tex_2(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f147,f44])).
% 0.21/0.47  fof(f147,plain,(
% 0.21/0.47    v2_struct_0(sK0) | ~v3_tex_2(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f146,f41])).
% 0.21/0.47  fof(f146,plain,(
% 0.21/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~v3_tex_2(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f145,f47])).
% 0.21/0.47  fof(f145,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~v3_tex_2(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f144,f45])).
% 0.21/0.47  fof(f144,plain,(
% 0.21/0.47    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | ~v3_tex_2(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 0.21/0.47    inference(resolution,[],[f142,f50])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v3_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | ~v3_tex_2(X1,X0) | v1_tops_1(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f13])).
% 0.21/0.47  fof(f13,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    v3_pre_topc(sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f141,f46])).
% 0.21/0.47  fof(f141,plain,(
% 0.21/0.47    v3_pre_topc(sK1,sK0) | ~v3_tdlat_3(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f140,f45])).
% 0.21/0.47  fof(f140,plain,(
% 0.21/0.47    ~v2_pre_topc(sK0) | v3_pre_topc(sK1,sK0) | ~v3_tdlat_3(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f139,f41])).
% 0.21/0.47  fof(f139,plain,(
% 0.21/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v3_pre_topc(sK1,sK0) | ~v3_tdlat_3(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f131,f47])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v3_pre_topc(sK1,sK0) | ~v3_tdlat_3(sK0)),
% 0.21/0.47    inference(resolution,[],[f129,f58])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v4_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | v3_pre_topc(X1,X0) | ~v3_tdlat_3(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((v3_pre_topc(X1,X0) | ~v4_pre_topc(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v4_pre_topc(X1,X0) => v3_pre_topc(X1,X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_tdlat_3)).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    m1_subset_1(sK5(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tdlat_3(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f80,f47])).
% 0.21/0.47  fof(f80,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | m1_subset_1(sK5(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tdlat_3(sK0)),
% 0.21/0.47    inference(resolution,[],[f45,f69])).
% 0.21/0.47  fof(f69,plain,(
% 0.21/0.47    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | m1_subset_1(sK5(X0),k1_zfmisc_1(u1_struct_0(X0))) | v1_tdlat_3(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f34])).
% 0.21/0.47  fof(f275,plain,(
% 0.21/0.47    ~m1_subset_1(sK5(sK0),k1_zfmisc_1(sK1)) | v3_pre_topc(sK5(sK0),sK0)),
% 0.21/0.47    inference(forward_demodulation,[],[f266,f264])).
% 0.21/0.47  fof(f264,plain,(
% 0.21/0.47    sK5(sK0) = k2_pre_topc(sK0,sK5(sK0))),
% 0.21/0.47    inference(forward_demodulation,[],[f256,f208])).
% 0.21/0.47  fof(f208,plain,(
% 0.21/0.47    sK5(sK0) = k9_subset_1(sK1,sK1,k2_pre_topc(sK0,sK5(sK0)))),
% 0.21/0.47    inference(resolution,[],[f164,f162])).
% 0.21/0.47  fof(f164,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | k9_subset_1(sK1,sK1,k2_pre_topc(sK0,X0)) = X0) )),
% 0.21/0.47    inference(forward_demodulation,[],[f163,f153])).
% 0.21/0.47  fof(f163,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f158,f74])).
% 0.21/0.47  fof(f74,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.47  fof(f158,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(sK1)) | ~r1_tarski(X0,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0) )),
% 0.21/0.47    inference(backward_demodulation,[],[f120,f153])).
% 0.21/0.47  fof(f120,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f119,f44])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 | v2_struct_0(sK0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f118,f41])).
% 0.21/0.47  fof(f118,plain,(
% 0.21/0.47    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 | v2_struct_0(sK0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f117,f47])).
% 0.21/0.47  fof(f117,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 | v2_struct_0(sK0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f111,f45])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,sK1) | k9_subset_1(u1_struct_0(sK0),sK1,k2_pre_topc(sK0,X0)) = X0 | v2_struct_0(sK0)) )),
% 0.21/0.47    inference(resolution,[],[f88,f75])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~v2_tex_2(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~r1_tarski(X2,X1) | k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | v2_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f37])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : (k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f36])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> ! [X2] : ((k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2 | ~r1_tarski(X2,X1)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,axiom,(
% 0.21/0.47    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v2_tex_2(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (r1_tarski(X2,X1) => k9_subset_1(u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_tex_2)).
% 0.21/0.47  fof(f88,plain,(
% 0.21/0.47    v2_tex_2(sK1,sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f87,f47])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f86,f41])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.47    inference(resolution,[],[f42,f56])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 0.21/0.47  fof(f256,plain,(
% 0.21/0.47    k2_pre_topc(sK0,sK5(sK0)) = k9_subset_1(sK1,sK1,k2_pre_topc(sK0,sK5(sK0)))),
% 0.21/0.47    inference(backward_demodulation,[],[f214,f254])).
% 0.21/0.47  fof(f254,plain,(
% 0.21/0.47    k2_pre_topc(sK0,sK5(sK0)) = k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0)))),
% 0.21/0.47    inference(forward_demodulation,[],[f253,f214])).
% 0.21/0.47  fof(f253,plain,(
% 0.21/0.47    k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))) = k9_subset_1(sK1,sK1,k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))))),
% 0.21/0.47    inference(forward_demodulation,[],[f248,f225])).
% 0.21/0.47  fof(f225,plain,(
% 0.21/0.47    k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))))),
% 0.21/0.47    inference(subsumption_resolution,[],[f224,f213])).
% 0.21/0.47  fof(f213,plain,(
% 0.21/0.47    m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))),k1_zfmisc_1(sK1))),
% 0.21/0.47    inference(resolution,[],[f211,f192])).
% 0.21/0.47  fof(f192,plain,(
% 0.21/0.47    ( ! [X9] : (~m1_subset_1(X9,k1_zfmisc_1(sK1)) | m1_subset_1(k2_pre_topc(sK0,X9),k1_zfmisc_1(sK1))) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f177,f47])).
% 0.21/0.47  fof(f177,plain,(
% 0.21/0.47    ( ! [X9] : (~m1_subset_1(X9,k1_zfmisc_1(sK1)) | ~l1_pre_topc(sK0) | m1_subset_1(k2_pre_topc(sK0,X9),k1_zfmisc_1(sK1))) )),
% 0.21/0.47    inference(superposition,[],[f79,f153])).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f39])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f38])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.21/0.47  fof(f211,plain,(
% 0.21/0.47    m1_subset_1(k2_pre_topc(sK0,sK5(sK0)),k1_zfmisc_1(sK1))),
% 0.21/0.47    inference(resolution,[],[f192,f162])).
% 0.21/0.47  fof(f224,plain,(
% 0.21/0.47    ~m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))),k1_zfmisc_1(sK1)) | k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))))),
% 0.21/0.47    inference(forward_demodulation,[],[f223,f153])).
% 0.21/0.47  fof(f223,plain,(
% 0.21/0.47    ~m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))))),
% 0.21/0.47    inference(subsumption_resolution,[],[f221,f47])).
% 0.21/0.47  fof(f221,plain,(
% 0.21/0.47    ~m1_subset_1(k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))) = k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))))),
% 0.21/0.47    inference(resolution,[],[f215,f67])).
% 0.21/0.47  fof(f215,plain,(
% 0.21/0.47    v4_pre_topc(k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))),sK0)),
% 0.21/0.47    inference(resolution,[],[f211,f179])).
% 0.21/0.47  fof(f179,plain,(
% 0.21/0.47    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(sK1)) | v4_pre_topc(k2_pre_topc(sK0,X2),sK0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f178,f45])).
% 0.21/0.47  fof(f178,plain,(
% 0.21/0.47    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(sK1)) | ~v2_pre_topc(sK0) | v4_pre_topc(k2_pre_topc(sK0,X2),sK0)) )),
% 0.21/0.47    inference(subsumption_resolution,[],[f170,f47])).
% 0.21/0.47  fof(f170,plain,(
% 0.21/0.47    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(sK1)) | ~l1_pre_topc(sK0) | ~v2_pre_topc(sK0) | v4_pre_topc(k2_pre_topc(sK0,X2),sK0)) )),
% 0.21/0.47    inference(superposition,[],[f57,f153])).
% 0.21/0.47  fof(f57,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v4_pre_topc(k2_pre_topc(X0,X1),X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.47    inference(flattening,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0,X1] : (v4_pre_topc(k2_pre_topc(X0,X1),X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_pre_topc(X0,X1),X0))),
% 0.21/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_tops_1)).
% 0.21/0.47  fof(f248,plain,(
% 0.21/0.47    k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))) = k9_subset_1(sK1,sK1,k2_pre_topc(sK0,k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0)))))),
% 0.21/0.47    inference(resolution,[],[f213,f164])).
% 0.21/0.47  fof(f214,plain,(
% 0.21/0.47    k2_pre_topc(sK0,sK5(sK0)) = k9_subset_1(sK1,sK1,k2_pre_topc(sK0,k2_pre_topc(sK0,sK5(sK0))))),
% 0.21/0.47    inference(resolution,[],[f211,f164])).
% 0.21/0.47  fof(f266,plain,(
% 0.21/0.47    v3_pre_topc(sK5(sK0),sK0) | ~m1_subset_1(k2_pre_topc(sK0,sK5(sK0)),k1_zfmisc_1(sK1))),
% 0.21/0.47    inference(backward_demodulation,[],[f206,f264])).
% 0.21/0.47  fof(f206,plain,(
% 0.21/0.47    ~m1_subset_1(k2_pre_topc(sK0,sK5(sK0)),k1_zfmisc_1(sK1)) | v3_pre_topc(k2_pre_topc(sK0,sK5(sK0)),sK0)),
% 0.21/0.47    inference(forward_demodulation,[],[f205,f153])).
% 0.21/0.47  fof(f205,plain,(
% 0.21/0.47    ~m1_subset_1(k2_pre_topc(sK0,sK5(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k2_pre_topc(sK0,sK5(sK0)),sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f204,f46])).
% 0.21/0.47  fof(f204,plain,(
% 0.21/0.47    ~m1_subset_1(k2_pre_topc(sK0,sK5(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k2_pre_topc(sK0,sK5(sK0)),sK0) | ~v3_tdlat_3(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f203,f45])).
% 0.21/0.47  fof(f203,plain,(
% 0.21/0.47    ~m1_subset_1(k2_pre_topc(sK0,sK5(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v3_pre_topc(k2_pre_topc(sK0,sK5(sK0)),sK0) | ~v3_tdlat_3(sK0)),
% 0.21/0.47    inference(subsumption_resolution,[],[f200,f47])).
% 0.21/0.47  fof(f200,plain,(
% 0.21/0.47    ~l1_pre_topc(sK0) | ~m1_subset_1(k2_pre_topc(sK0,sK5(sK0)),k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_pre_topc(sK0) | v3_pre_topc(k2_pre_topc(sK0,sK5(sK0)),sK0) | ~v3_tdlat_3(sK0)),
% 0.21/0.47    inference(resolution,[],[f196,f58])).
% 0.21/0.47  fof(f196,plain,(
% 0.21/0.47    v4_pre_topc(k2_pre_topc(sK0,sK5(sK0)),sK0)),
% 0.21/0.47    inference(resolution,[],[f179,f162])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (20601)------------------------------
% 0.21/0.47  % (20601)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (20601)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (20601)Memory used [KB]: 6268
% 0.21/0.47  % (20601)Time elapsed: 0.071 s
% 0.21/0.47  % (20601)------------------------------
% 0.21/0.47  % (20601)------------------------------
% 0.21/0.47  % (20609)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.48  % (20595)Success in time 0.117 s
%------------------------------------------------------------------------------
