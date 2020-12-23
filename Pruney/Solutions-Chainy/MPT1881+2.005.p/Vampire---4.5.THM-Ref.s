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
% DateTime   : Thu Dec  3 13:21:53 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  158 (4056 expanded)
%              Number of leaves         :   16 ( 798 expanded)
%              Depth                    :   39
%              Number of atoms          :  632 (17024 expanded)
%              Number of equality atoms :  109 (1238 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f363,plain,(
    $false ),
    inference(subsumption_resolution,[],[f361,f360])).

fof(f360,plain,(
    v1_subset_1(sK1,sK1) ),
    inference(subsumption_resolution,[],[f359,f346])).

fof(f346,plain,(
    sK1 = k2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f336])).

fof(f336,plain,
    ( sK1 = k2_struct_0(sK0)
    | sK1 = k2_struct_0(sK0)
    | sK1 = k2_struct_0(sK0) ),
    inference(superposition,[],[f335,f236])).

fof(f236,plain,
    ( k2_struct_0(sK0) = k2_pre_topc(sK0,sK1)
    | sK1 = k2_struct_0(sK0) ),
    inference(forward_demodulation,[],[f235,f149])).

fof(f149,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f125,f58])).

fof(f58,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f125,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f55,f59])).

fof(f59,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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

fof(f235,plain,
    ( sK1 = k2_struct_0(sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f234,f153])).

fof(f153,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f51,f149])).

fof(f51,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f22])).

fof(f234,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | sK1 = k2_struct_0(sK0)
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(forward_demodulation,[],[f233,f149])).

fof(f233,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f232,f55])).

fof(f232,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f229,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = k2_pre_topc(X0,X1)
      | ~ v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).

fof(f229,plain,
    ( v1_tops_1(sK1,sK0)
    | sK1 = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f228,f153])).

fof(f228,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | sK1 = k2_struct_0(sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f227,f149])).

fof(f227,plain,
    ( sK1 = k2_struct_0(sK0)
    | v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f226,f54])).

fof(f54,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f226,plain,
    ( sK1 = k2_struct_0(sK0)
    | v1_tops_1(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f225,f55])).

fof(f225,plain,
    ( sK1 = k2_struct_0(sK0)
    | v1_tops_1(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f224,f53])).

fof(f53,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f224,plain,
    ( sK1 = k2_struct_0(sK0)
    | v1_tops_1(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tdlat_3(sK0) ),
    inference(resolution,[],[f203,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(X1,X0)
      | ~ v1_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( v3_pre_topc(X1,X0)
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ( v1_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => v3_pre_topc(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).

fof(f203,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | sK1 = k2_struct_0(sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f202,f153])).

fof(f202,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | sK1 = k2_struct_0(sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(forward_demodulation,[],[f201,f149])).

fof(f201,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f200,f55])).

fof(f200,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f199,f53])).

fof(f199,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f193,f52])).

fof(f52,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f193,plain,
    ( sK1 = k2_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0)
    | v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f190,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X1,X0)
      | ~ v3_tex_2(X1,X0)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_tops_1(X1,X0)
          | ~ v3_tex_2(X1,X0)
          | ~ v3_pre_topc(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
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
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( v3_tex_2(X1,X0)
              & v3_pre_topc(X1,X0) )
           => v1_tops_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).

fof(f190,plain,
    ( v3_tex_2(sK1,sK0)
    | sK1 = k2_struct_0(sK0) ),
    inference(resolution,[],[f154,f151])).

fof(f151,plain,
    ( ~ v1_subset_1(sK1,k2_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(backward_demodulation,[],[f49,f149])).

fof(f49,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f154,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | sK1 = k2_struct_0(sK0) ),
    inference(resolution,[],[f153,f83])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f335,plain,
    ( sK1 = k2_pre_topc(sK0,sK1)
    | sK1 = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f334,f153])).

fof(f334,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | sK1 = k2_struct_0(sK0)
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(forward_demodulation,[],[f333,f149])).

fof(f333,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f332,f55])).

fof(f332,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f328,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
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

fof(f328,plain,
    ( v4_pre_topc(sK1,sK0)
    | sK1 = k2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f325])).

fof(f325,plain,
    ( v4_pre_topc(sK1,sK0)
    | sK1 = k2_struct_0(sK0)
    | sK1 = k2_struct_0(sK0) ),
    inference(superposition,[],[f294,f272])).

fof(f272,plain,
    ( sK1 = u1_struct_0(sK2(sK0,sK1))
    | sK1 = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f271,f55])).

fof(f271,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 = k2_struct_0(sK0)
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f270,f52])).

fof(f270,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | sK1 = k2_struct_0(sK0)
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f269,f153])).

fof(f269,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | sK1 = k2_struct_0(sK0)
    | sK1 = u1_struct_0(sK2(sK0,sK1)) ),
    inference(superposition,[],[f207,f149])).

fof(f207,plain,(
    ! [X3] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3)))
      | v2_struct_0(X3)
      | ~ l1_pre_topc(X3)
      | sK1 = k2_struct_0(sK0)
      | sK1 = u1_struct_0(sK2(X3,sK1)) ) ),
    inference(resolution,[],[f198,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(sK2(X0,X1)) = X1 ) ),
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

fof(f198,plain,
    ( ~ v1_xboole_0(sK1)
    | sK1 = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f197,f153])).

fof(f197,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | sK1 = k2_struct_0(sK0)
    | ~ v1_xboole_0(sK1) ),
    inference(forward_demodulation,[],[f196,f149])).

fof(f196,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f195,f55])).

fof(f195,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f194,f53])).

fof(f194,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f192,f52])).

fof(f192,plain,
    ( sK1 = k2_struct_0(sK0)
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f190,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ~ v3_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
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
            & v1_xboole_0(X1) )
         => ~ v3_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).

fof(f294,plain,
    ( v4_pre_topc(u1_struct_0(sK2(sK0,sK1)),sK0)
    | sK1 = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f293,f282])).

fof(f282,plain,
    ( m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(k2_struct_0(sK0)))
    | sK1 = k2_struct_0(sK0) ),
    inference(forward_demodulation,[],[f281,f149])).

fof(f281,plain,
    ( sK1 = k2_struct_0(sK0)
    | m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f280,f55])).

fof(f280,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f266,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f266,plain,
    ( m1_pre_topc(sK2(sK0,sK1),sK0)
    | sK1 = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f265,f55])).

fof(f265,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 = k2_struct_0(sK0)
    | m1_pre_topc(sK2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f264,f52])).

fof(f264,plain,
    ( v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | sK1 = k2_struct_0(sK0)
    | m1_pre_topc(sK2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f263,f153])).

fof(f263,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | sK1 = k2_struct_0(sK0)
    | m1_pre_topc(sK2(sK0,sK1),sK0) ),
    inference(superposition,[],[f206,f149])).

fof(f206,plain,(
    ! [X2] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2)))
      | v2_struct_0(X2)
      | ~ l1_pre_topc(X2)
      | sK1 = k2_struct_0(sK0)
      | m1_pre_topc(sK2(X2,sK1),X2) ) ),
    inference(resolution,[],[f198,f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_pre_topc(sK2(X0,X1),X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f293,plain,
    ( ~ m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(k2_struct_0(sK0)))
    | sK1 = k2_struct_0(sK0)
    | v4_pre_topc(u1_struct_0(sK2(sK0,sK1)),sK0) ),
    inference(forward_demodulation,[],[f292,f149])).

fof(f292,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(u1_struct_0(sK2(sK0,sK1)),sK0) ),
    inference(subsumption_resolution,[],[f291,f266])).

fof(f291,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(u1_struct_0(sK2(sK0,sK1)),sK0)
    | ~ m1_pre_topc(sK2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f290,f55])).

fof(f290,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(u1_struct_0(sK2(sK0,sK1)),sK0)
    | ~ m1_pre_topc(sK2(sK0,sK1),sK0) ),
    inference(subsumption_resolution,[],[f289,f53])).

fof(f289,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v4_pre_topc(u1_struct_0(sK2(sK0,sK1)),sK0)
    | ~ m1_pre_topc(sK2(sK0,sK1),sK0) ),
    inference(resolution,[],[f273,f86])).

fof(f86,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v4_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(equality_resolution,[],[f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v4_pre_topc(X2,X0)
      | ~ v1_borsuk_1(X1,X0)
      | ~ m1_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( ( m1_pre_topc(X1,X0)
                  & v1_borsuk_1(X1,X0) )
              <=> v4_pre_topc(X2,X0) )
              | u1_struct_0(X1) != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
             => ( u1_struct_0(X1) = X2
               => ( ( m1_pre_topc(X1,X0)
                    & v1_borsuk_1(X1,X0) )
                <=> v4_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tsep_1)).

fof(f273,plain,
    ( v1_borsuk_1(sK2(sK0,sK1),sK0)
    | sK1 = k2_struct_0(sK0) ),
    inference(resolution,[],[f266,f101])).

fof(f101,plain,(
    ! [X7] :
      ( ~ m1_pre_topc(X7,sK0)
      | v1_borsuk_1(X7,sK0) ) ),
    inference(subsumption_resolution,[],[f100,f55])).

fof(f100,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X7,sK0)
      | v1_borsuk_1(X7,sK0) ) ),
    inference(subsumption_resolution,[],[f99,f54])).

fof(f99,plain,(
    ! [X7] :
      ( ~ v1_tdlat_3(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X7,sK0)
      | v1_borsuk_1(X7,sK0) ) ),
    inference(subsumption_resolution,[],[f95,f53])).

fof(f95,plain,(
    ! [X7] :
      ( ~ v2_pre_topc(sK0)
      | ~ v1_tdlat_3(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_pre_topc(X7,sK0)
      | v1_borsuk_1(X7,sK0) ) ),
    inference(resolution,[],[f52,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | v1_borsuk_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tdlat_3(X1)
            & v1_tsep_1(X1,X0)
            & v1_borsuk_1(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_tdlat_3)).

fof(f359,plain,
    ( sK1 != k2_struct_0(sK0)
    | v1_subset_1(sK1,sK1) ),
    inference(forward_demodulation,[],[f356,f347])).

fof(f347,plain,(
    sK1 = k2_pre_topc(sK0,sK1) ),
    inference(backward_demodulation,[],[f126,f346])).

fof(f126,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f55,f60])).

fof(f60,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).

fof(f356,plain,
    ( v1_subset_1(sK1,sK1)
    | k2_struct_0(sK0) != k2_pre_topc(sK0,sK1) ),
    inference(backward_demodulation,[],[f220,f346])).

fof(f220,plain,
    ( k2_struct_0(sK0) != k2_pre_topc(sK0,sK1)
    | v1_subset_1(sK1,k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f219,f149])).

fof(f219,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | u1_struct_0(sK0) != k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f218,f153])).

fof(f218,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_subset_1(sK1,k2_struct_0(sK0))
    | u1_struct_0(sK0) != k2_pre_topc(sK0,sK1) ),
    inference(forward_demodulation,[],[f217,f149])).

fof(f217,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) != k2_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f216,f55])).

fof(f216,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_struct_0(sK0) != k2_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f214,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f214,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | v1_subset_1(sK1,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f213,f153])).

fof(f213,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v1_tops_1(sK1,sK0)
    | v1_subset_1(sK1,k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f212,f149])).

fof(f212,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f211,f55])).

fof(f211,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f210,f54])).

fof(f210,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f209,f53])).

fof(f209,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f208,f52])).

fof(f208,plain,
    ( ~ v1_tops_1(sK1,sK0)
    | v1_subset_1(sK1,k2_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f185,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

fof(f185,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ v1_tops_1(sK1,sK0)
    | v1_subset_1(sK1,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f184,f153])).

fof(f184,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ v1_tops_1(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(forward_demodulation,[],[f183,f149])).

fof(f183,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tops_1(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f182,f55])).

fof(f182,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tops_1(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f181,f53])).

fof(f181,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tops_1(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f180,f52])).

fof(f180,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | v2_struct_0(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v1_tops_1(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f152,f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f152,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | v1_subset_1(sK1,k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f50,f149])).

fof(f50,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f22])).

fof(f361,plain,(
    ~ v1_subset_1(sK1,sK1) ),
    inference(resolution,[],[f352,f87])).

fof(f87,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f352,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(backward_demodulation,[],[f153,f346])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % WCLimit    : 600
% 0.13/0.33  % DateTime   : Tue Dec  1 19:24:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.42  % (21983)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.42  % (21983)Refutation found. Thanks to Tanya!
% 0.20/0.42  % SZS status Theorem for theBenchmark
% 0.20/0.43  % (21974)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.43  % SZS output start Proof for theBenchmark
% 0.20/0.43  fof(f363,plain,(
% 0.20/0.43    $false),
% 0.20/0.43    inference(subsumption_resolution,[],[f361,f360])).
% 0.20/0.43  fof(f360,plain,(
% 0.20/0.43    v1_subset_1(sK1,sK1)),
% 0.20/0.43    inference(subsumption_resolution,[],[f359,f346])).
% 0.20/0.43  fof(f346,plain,(
% 0.20/0.43    sK1 = k2_struct_0(sK0)),
% 0.20/0.43    inference(duplicate_literal_removal,[],[f336])).
% 0.20/0.43  fof(f336,plain,(
% 0.20/0.43    sK1 = k2_struct_0(sK0) | sK1 = k2_struct_0(sK0) | sK1 = k2_struct_0(sK0)),
% 0.20/0.43    inference(superposition,[],[f335,f236])).
% 0.20/0.43  fof(f236,plain,(
% 0.20/0.43    k2_struct_0(sK0) = k2_pre_topc(sK0,sK1) | sK1 = k2_struct_0(sK0)),
% 0.20/0.43    inference(forward_demodulation,[],[f235,f149])).
% 0.20/0.43  fof(f149,plain,(
% 0.20/0.43    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.20/0.43    inference(resolution,[],[f125,f58])).
% 0.20/0.43  fof(f58,plain,(
% 0.20/0.43    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f23])).
% 0.20/0.43  fof(f23,plain,(
% 0.20/0.43    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f3])).
% 0.20/0.43  fof(f3,axiom,(
% 0.20/0.43    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.43  fof(f125,plain,(
% 0.20/0.43    l1_struct_0(sK0)),
% 0.20/0.43    inference(resolution,[],[f55,f59])).
% 0.20/0.43  fof(f59,plain,(
% 0.20/0.43    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f24])).
% 0.20/0.43  fof(f24,plain,(
% 0.20/0.43    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f4])).
% 0.20/0.43  fof(f4,axiom,(
% 0.20/0.43    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.20/0.43  fof(f55,plain,(
% 0.20/0.43    l1_pre_topc(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f22])).
% 0.20/0.43  fof(f22,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f21])).
% 0.20/0.43  fof(f21,plain,(
% 0.20/0.43    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f20])).
% 0.20/0.43  fof(f20,negated_conjecture,(
% 0.20/0.43    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.20/0.43    inference(negated_conjecture,[],[f19])).
% 0.20/0.43  fof(f19,conjecture,(
% 0.20/0.43    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).
% 0.20/0.43  fof(f235,plain,(
% 0.20/0.43    sK1 = k2_struct_0(sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.20/0.43    inference(subsumption_resolution,[],[f234,f153])).
% 0.20/0.43  fof(f153,plain,(
% 0.20/0.43    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.20/0.43    inference(backward_demodulation,[],[f51,f149])).
% 0.20/0.43  fof(f51,plain,(
% 0.20/0.43    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.43    inference(cnf_transformation,[],[f22])).
% 0.20/0.43  fof(f234,plain,(
% 0.20/0.43    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | sK1 = k2_struct_0(sK0) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.20/0.43    inference(forward_demodulation,[],[f233,f149])).
% 0.20/0.43  fof(f233,plain,(
% 0.20/0.43    sK1 = k2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.20/0.43    inference(subsumption_resolution,[],[f232,f55])).
% 0.20/0.43  fof(f232,plain,(
% 0.20/0.43    sK1 = k2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = k2_pre_topc(sK0,sK1)),
% 0.20/0.43    inference(resolution,[],[f229,f66])).
% 0.20/0.43  fof(f66,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = k2_pre_topc(X0,X1) | ~v1_tops_1(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f31])).
% 0.20/0.43  fof(f31,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f11])).
% 0.20/0.43  fof(f11,axiom,(
% 0.20/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tops_3)).
% 0.20/0.43  fof(f229,plain,(
% 0.20/0.43    v1_tops_1(sK1,sK0) | sK1 = k2_struct_0(sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f228,f153])).
% 0.20/0.43  fof(f228,plain,(
% 0.20/0.43    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | sK1 = k2_struct_0(sK0) | v1_tops_1(sK1,sK0)),
% 0.20/0.43    inference(forward_demodulation,[],[f227,f149])).
% 0.20/0.43  fof(f227,plain,(
% 0.20/0.43    sK1 = k2_struct_0(sK0) | v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.43    inference(subsumption_resolution,[],[f226,f54])).
% 0.20/0.43  fof(f54,plain,(
% 0.20/0.43    v1_tdlat_3(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f22])).
% 0.20/0.43  fof(f226,plain,(
% 0.20/0.43    sK1 = k2_struct_0(sK0) | v1_tops_1(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tdlat_3(sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f225,f55])).
% 0.20/0.43  fof(f225,plain,(
% 0.20/0.43    sK1 = k2_struct_0(sK0) | v1_tops_1(sK1,sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tdlat_3(sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f224,f53])).
% 0.20/0.43  fof(f53,plain,(
% 0.20/0.43    v2_pre_topc(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f22])).
% 0.20/0.43  fof(f224,plain,(
% 0.20/0.43    sK1 = k2_struct_0(sK0) | v1_tops_1(sK1,sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tdlat_3(sK0)),
% 0.20/0.43    inference(resolution,[],[f203,f78])).
% 0.20/0.43  fof(f78,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(X1,X0) | ~v1_tdlat_3(X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f45])).
% 0.20/0.43  fof(f45,plain,(
% 0.20/0.43    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.43    inference(flattening,[],[f44])).
% 0.20/0.43  fof(f44,plain,(
% 0.20/0.43    ! [X0] : ((v1_tdlat_3(X0) <=> ! [X1] : (v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f14])).
% 0.20/0.43  fof(f14,axiom,(
% 0.20/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => (v1_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v3_pre_topc(X1,X0))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_tdlat_3)).
% 0.20/0.43  fof(f203,plain,(
% 0.20/0.43    ~v3_pre_topc(sK1,sK0) | sK1 = k2_struct_0(sK0) | v1_tops_1(sK1,sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f202,f153])).
% 0.20/0.43  fof(f202,plain,(
% 0.20/0.43    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | sK1 = k2_struct_0(sK0) | ~v3_pre_topc(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 0.20/0.43    inference(forward_demodulation,[],[f201,f149])).
% 0.20/0.43  fof(f201,plain,(
% 0.20/0.43    sK1 = k2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f200,f55])).
% 0.20/0.43  fof(f200,plain,(
% 0.20/0.43    sK1 = k2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f199,f53])).
% 0.20/0.43  fof(f199,plain,(
% 0.20/0.43    sK1 = k2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f193,f52])).
% 0.20/0.43  fof(f52,plain,(
% 0.20/0.43    ~v2_struct_0(sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f22])).
% 0.20/0.43  fof(f193,plain,(
% 0.20/0.43    sK1 = k2_struct_0(sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0) | v1_tops_1(sK1,sK0)),
% 0.20/0.43    inference(resolution,[],[f190,f71])).
% 0.20/0.43  fof(f71,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X1,X0) | ~v3_tex_2(X1,X0) | v1_tops_1(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f35])).
% 0.20/0.43  fof(f35,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (v1_tops_1(X1,X0) | ~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f34])).
% 0.20/0.43  fof(f34,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) | (~v3_tex_2(X1,X0) | ~v3_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f17])).
% 0.20/0.43  fof(f17,axiom,(
% 0.20/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v3_tex_2(X1,X0) & v3_pre_topc(X1,X0)) => v1_tops_1(X1,X0))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_tex_2)).
% 0.20/0.43  fof(f190,plain,(
% 0.20/0.43    v3_tex_2(sK1,sK0) | sK1 = k2_struct_0(sK0)),
% 0.20/0.43    inference(resolution,[],[f154,f151])).
% 0.20/0.43  fof(f151,plain,(
% 0.20/0.43    ~v1_subset_1(sK1,k2_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 0.20/0.43    inference(backward_demodulation,[],[f49,f149])).
% 0.20/0.43  fof(f49,plain,(
% 0.20/0.43    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f22])).
% 0.20/0.43  fof(f154,plain,(
% 0.20/0.43    v1_subset_1(sK1,k2_struct_0(sK0)) | sK1 = k2_struct_0(sK0)),
% 0.20/0.43    inference(resolution,[],[f153,f83])).
% 0.20/0.43  fof(f83,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f48])).
% 0.20/0.43  fof(f48,plain,(
% 0.20/0.43    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f12])).
% 0.20/0.43  fof(f12,axiom,(
% 0.20/0.43    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.20/0.43  fof(f335,plain,(
% 0.20/0.43    sK1 = k2_pre_topc(sK0,sK1) | sK1 = k2_struct_0(sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f334,f153])).
% 0.20/0.43  fof(f334,plain,(
% 0.20/0.43    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | sK1 = k2_struct_0(sK0) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.20/0.43    inference(forward_demodulation,[],[f333,f149])).
% 0.20/0.43  fof(f333,plain,(
% 0.20/0.43    sK1 = k2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.20/0.43    inference(subsumption_resolution,[],[f332,f55])).
% 0.20/0.43  fof(f332,plain,(
% 0.20/0.43    sK1 = k2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = k2_pre_topc(sK0,sK1)),
% 0.20/0.43    inference(resolution,[],[f328,f64])).
% 0.20/0.43  fof(f64,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 0.20/0.43    inference(cnf_transformation,[],[f30])).
% 0.20/0.43  fof(f30,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(flattening,[],[f29])).
% 0.20/0.43  fof(f29,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f5])).
% 0.20/0.43  fof(f5,axiom,(
% 0.20/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.20/0.43  fof(f328,plain,(
% 0.20/0.43    v4_pre_topc(sK1,sK0) | sK1 = k2_struct_0(sK0)),
% 0.20/0.43    inference(duplicate_literal_removal,[],[f325])).
% 0.20/0.43  fof(f325,plain,(
% 0.20/0.43    v4_pre_topc(sK1,sK0) | sK1 = k2_struct_0(sK0) | sK1 = k2_struct_0(sK0)),
% 0.20/0.43    inference(superposition,[],[f294,f272])).
% 0.20/0.43  fof(f272,plain,(
% 0.20/0.43    sK1 = u1_struct_0(sK2(sK0,sK1)) | sK1 = k2_struct_0(sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f271,f55])).
% 0.20/0.43  fof(f271,plain,(
% 0.20/0.43    ~l1_pre_topc(sK0) | sK1 = k2_struct_0(sK0) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.20/0.43    inference(subsumption_resolution,[],[f270,f52])).
% 0.20/0.43  fof(f270,plain,(
% 0.20/0.43    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | sK1 = k2_struct_0(sK0) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.20/0.43    inference(subsumption_resolution,[],[f269,f153])).
% 0.20/0.43  fof(f269,plain,(
% 0.20/0.43    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | sK1 = k2_struct_0(sK0) | sK1 = u1_struct_0(sK2(sK0,sK1))),
% 0.20/0.43    inference(superposition,[],[f207,f149])).
% 0.20/0.43  fof(f207,plain,(
% 0.20/0.43    ( ! [X3] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X3))) | v2_struct_0(X3) | ~l1_pre_topc(X3) | sK1 = k2_struct_0(sK0) | sK1 = u1_struct_0(sK2(X3,sK1))) )),
% 0.20/0.43    inference(resolution,[],[f198,f70])).
% 0.20/0.43  fof(f70,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(sK2(X0,X1)) = X1) )),
% 0.20/0.43    inference(cnf_transformation,[],[f33])).
% 0.20/0.43  fof(f33,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f32])).
% 0.20/0.43  fof(f32,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f13])).
% 0.20/0.43  fof(f13,axiom,(
% 0.20/0.43    ! [X0] : ((l1_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => ? [X2] : (u1_struct_0(X2) = X1 & m1_pre_topc(X2,X0) & v1_pre_topc(X2) & ~v2_struct_0(X2))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_tsep_1)).
% 0.20/0.43  fof(f198,plain,(
% 0.20/0.43    ~v1_xboole_0(sK1) | sK1 = k2_struct_0(sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f197,f153])).
% 0.20/0.43  fof(f197,plain,(
% 0.20/0.43    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | sK1 = k2_struct_0(sK0) | ~v1_xboole_0(sK1)),
% 0.20/0.43    inference(forward_demodulation,[],[f196,f149])).
% 0.20/0.43  fof(f196,plain,(
% 0.20/0.43    sK1 = k2_struct_0(sK0) | ~v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.43    inference(subsumption_resolution,[],[f195,f55])).
% 0.20/0.43  fof(f195,plain,(
% 0.20/0.43    sK1 = k2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.43    inference(subsumption_resolution,[],[f194,f53])).
% 0.20/0.43  fof(f194,plain,(
% 0.20/0.43    sK1 = k2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.43    inference(subsumption_resolution,[],[f192,f52])).
% 0.20/0.43  fof(f192,plain,(
% 0.20/0.43    sK1 = k2_struct_0(sK0) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.43    inference(resolution,[],[f190,f73])).
% 0.20/0.43  fof(f73,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_tex_2(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f39])).
% 0.20/0.43  fof(f39,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f38])).
% 0.20/0.43  fof(f38,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (~v3_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f16])).
% 0.20/0.43  fof(f16,axiom,(
% 0.20/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => ~v3_tex_2(X1,X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_tex_2)).
% 0.20/0.43  fof(f294,plain,(
% 0.20/0.43    v4_pre_topc(u1_struct_0(sK2(sK0,sK1)),sK0) | sK1 = k2_struct_0(sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f293,f282])).
% 0.20/0.43  fof(f282,plain,(
% 0.20/0.43    m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(k2_struct_0(sK0))) | sK1 = k2_struct_0(sK0)),
% 0.20/0.43    inference(forward_demodulation,[],[f281,f149])).
% 0.20/0.43  fof(f281,plain,(
% 0.20/0.43    sK1 = k2_struct_0(sK0) | m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.43    inference(subsumption_resolution,[],[f280,f55])).
% 0.20/0.43  fof(f280,plain,(
% 0.20/0.43    sK1 = k2_struct_0(sK0) | ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.43    inference(resolution,[],[f266,f62])).
% 0.20/0.43  fof(f62,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f28])).
% 0.20/0.43  fof(f28,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f8])).
% 0.20/0.43  fof(f8,axiom,(
% 0.20/0.43    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.20/0.43  fof(f266,plain,(
% 0.20/0.43    m1_pre_topc(sK2(sK0,sK1),sK0) | sK1 = k2_struct_0(sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f265,f55])).
% 0.20/0.43  fof(f265,plain,(
% 0.20/0.43    ~l1_pre_topc(sK0) | sK1 = k2_struct_0(sK0) | m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f264,f52])).
% 0.20/0.43  fof(f264,plain,(
% 0.20/0.43    v2_struct_0(sK0) | ~l1_pre_topc(sK0) | sK1 = k2_struct_0(sK0) | m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f263,f153])).
% 0.20/0.43  fof(f263,plain,(
% 0.20/0.43    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | sK1 = k2_struct_0(sK0) | m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.20/0.43    inference(superposition,[],[f206,f149])).
% 0.20/0.43  fof(f206,plain,(
% 0.20/0.43    ( ! [X2] : (~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X2))) | v2_struct_0(X2) | ~l1_pre_topc(X2) | sK1 = k2_struct_0(sK0) | m1_pre_topc(sK2(X2,sK1),X2)) )),
% 0.20/0.43    inference(resolution,[],[f198,f69])).
% 0.20/0.43  fof(f69,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_pre_topc(sK2(X0,X1),X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f33])).
% 0.20/0.43  fof(f293,plain,(
% 0.20/0.43    ~m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(k2_struct_0(sK0))) | sK1 = k2_struct_0(sK0) | v4_pre_topc(u1_struct_0(sK2(sK0,sK1)),sK0)),
% 0.20/0.43    inference(forward_demodulation,[],[f292,f149])).
% 0.20/0.43  fof(f292,plain,(
% 0.20/0.43    sK1 = k2_struct_0(sK0) | ~m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(u1_struct_0(sK2(sK0,sK1)),sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f291,f266])).
% 0.20/0.43  fof(f291,plain,(
% 0.20/0.43    sK1 = k2_struct_0(sK0) | ~m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(u1_struct_0(sK2(sK0,sK1)),sK0) | ~m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f290,f55])).
% 0.20/0.43  fof(f290,plain,(
% 0.20/0.43    sK1 = k2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(u1_struct_0(sK2(sK0,sK1)),sK0) | ~m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f289,f53])).
% 0.20/0.43  fof(f289,plain,(
% 0.20/0.43    sK1 = k2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(u1_struct_0(sK2(sK0,sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v4_pre_topc(u1_struct_0(sK2(sK0,sK1)),sK0) | ~m1_pre_topc(sK2(sK0,sK1),sK0)),
% 0.20/0.43    inference(resolution,[],[f273,f86])).
% 0.20/0.43  fof(f86,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v4_pre_topc(u1_struct_0(X1),X0) | ~v1_borsuk_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.20/0.43    inference(equality_resolution,[],[f81])).
% 0.20/0.43  fof(f81,plain,(
% 0.20/0.43    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v4_pre_topc(X2,X0) | ~v1_borsuk_1(X1,X0) | ~m1_pre_topc(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f47])).
% 0.20/0.43  fof(f47,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : (((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.20/0.43    inference(flattening,[],[f46])).
% 0.20/0.43  fof(f46,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (! [X2] : ((((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0)) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f7])).
% 0.20/0.43  fof(f7,axiom,(
% 0.20/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => ((m1_pre_topc(X1,X0) & v1_borsuk_1(X1,X0)) <=> v4_pre_topc(X2,X0))))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_tsep_1)).
% 0.20/0.43  fof(f273,plain,(
% 0.20/0.43    v1_borsuk_1(sK2(sK0,sK1),sK0) | sK1 = k2_struct_0(sK0)),
% 0.20/0.43    inference(resolution,[],[f266,f101])).
% 0.20/0.43  fof(f101,plain,(
% 0.20/0.43    ( ! [X7] : (~m1_pre_topc(X7,sK0) | v1_borsuk_1(X7,sK0)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f100,f55])).
% 0.20/0.43  fof(f100,plain,(
% 0.20/0.43    ( ! [X7] : (~l1_pre_topc(sK0) | ~m1_pre_topc(X7,sK0) | v1_borsuk_1(X7,sK0)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f99,f54])).
% 0.20/0.43  fof(f99,plain,(
% 0.20/0.43    ( ! [X7] : (~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X7,sK0) | v1_borsuk_1(X7,sK0)) )),
% 0.20/0.43    inference(subsumption_resolution,[],[f95,f53])).
% 0.20/0.43  fof(f95,plain,(
% 0.20/0.43    ( ! [X7] : (~v2_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~m1_pre_topc(X7,sK0) | v1_borsuk_1(X7,sK0)) )),
% 0.20/0.43    inference(resolution,[],[f52,f74])).
% 0.20/0.43  fof(f74,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | v1_borsuk_1(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f41])).
% 0.20/0.43  fof(f41,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f40])).
% 0.20/0.43  fof(f40,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : ((v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0)) | ~m1_pre_topc(X1,X0)) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f10])).
% 0.20/0.43  fof(f10,axiom,(
% 0.20/0.43    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tdlat_3(X1) & v1_tsep_1(X1,X0) & v1_borsuk_1(X1,X0))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_tdlat_3)).
% 0.20/0.43  fof(f359,plain,(
% 0.20/0.43    sK1 != k2_struct_0(sK0) | v1_subset_1(sK1,sK1)),
% 0.20/0.43    inference(forward_demodulation,[],[f356,f347])).
% 0.20/0.43  fof(f347,plain,(
% 0.20/0.43    sK1 = k2_pre_topc(sK0,sK1)),
% 0.20/0.43    inference(backward_demodulation,[],[f126,f346])).
% 0.20/0.43  fof(f126,plain,(
% 0.20/0.43    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))),
% 0.20/0.43    inference(resolution,[],[f55,f60])).
% 0.20/0.43  fof(f60,plain,(
% 0.20/0.43    ( ! [X0] : (~l1_pre_topc(X0) | k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0))) )),
% 0.20/0.43    inference(cnf_transformation,[],[f25])).
% 0.20/0.43  fof(f25,plain,(
% 0.20/0.43    ! [X0] : (k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)) | ~l1_pre_topc(X0))),
% 0.20/0.43    inference(ennf_transformation,[],[f6])).
% 0.20/0.43  fof(f6,axiom,(
% 0.20/0.43    ! [X0] : (l1_pre_topc(X0) => k2_struct_0(X0) = k2_pre_topc(X0,k2_struct_0(X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_tops_1)).
% 0.20/0.43  fof(f356,plain,(
% 0.20/0.43    v1_subset_1(sK1,sK1) | k2_struct_0(sK0) != k2_pre_topc(sK0,sK1)),
% 0.20/0.43    inference(backward_demodulation,[],[f220,f346])).
% 0.20/0.43  fof(f220,plain,(
% 0.20/0.43    k2_struct_0(sK0) != k2_pre_topc(sK0,sK1) | v1_subset_1(sK1,k2_struct_0(sK0))),
% 0.20/0.43    inference(forward_demodulation,[],[f219,f149])).
% 0.20/0.43  fof(f219,plain,(
% 0.20/0.43    v1_subset_1(sK1,k2_struct_0(sK0)) | u1_struct_0(sK0) != k2_pre_topc(sK0,sK1)),
% 0.20/0.43    inference(subsumption_resolution,[],[f218,f153])).
% 0.20/0.43  fof(f218,plain,(
% 0.20/0.43    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v1_subset_1(sK1,k2_struct_0(sK0)) | u1_struct_0(sK0) != k2_pre_topc(sK0,sK1)),
% 0.20/0.43    inference(forward_demodulation,[],[f217,f149])).
% 0.20/0.43  fof(f217,plain,(
% 0.20/0.43    v1_subset_1(sK1,k2_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) != k2_pre_topc(sK0,sK1)),
% 0.20/0.43    inference(subsumption_resolution,[],[f216,f55])).
% 0.20/0.43  fof(f216,plain,(
% 0.20/0.43    v1_subset_1(sK1,k2_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) != k2_pre_topc(sK0,sK1)),
% 0.20/0.43    inference(resolution,[],[f214,f65])).
% 0.20/0.43  fof(f65,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) != k2_pre_topc(X0,X1) | v1_tops_1(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f31])).
% 0.20/0.43  fof(f214,plain,(
% 0.20/0.43    ~v1_tops_1(sK1,sK0) | v1_subset_1(sK1,k2_struct_0(sK0))),
% 0.20/0.43    inference(subsumption_resolution,[],[f213,f153])).
% 0.20/0.43  fof(f213,plain,(
% 0.20/0.43    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(sK1,sK0) | v1_subset_1(sK1,k2_struct_0(sK0))),
% 0.20/0.43    inference(forward_demodulation,[],[f212,f149])).
% 0.20/0.43  fof(f212,plain,(
% 0.20/0.43    ~v1_tops_1(sK1,sK0) | v1_subset_1(sK1,k2_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.43    inference(subsumption_resolution,[],[f211,f55])).
% 0.20/0.43  fof(f211,plain,(
% 0.20/0.43    ~v1_tops_1(sK1,sK0) | v1_subset_1(sK1,k2_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.43    inference(subsumption_resolution,[],[f210,f54])).
% 0.20/0.43  fof(f210,plain,(
% 0.20/0.43    ~v1_tops_1(sK1,sK0) | v1_subset_1(sK1,k2_struct_0(sK0)) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.43    inference(subsumption_resolution,[],[f209,f53])).
% 0.20/0.43  fof(f209,plain,(
% 0.20/0.43    ~v1_tops_1(sK1,sK0) | v1_subset_1(sK1,k2_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.43    inference(subsumption_resolution,[],[f208,f52])).
% 0.20/0.43  fof(f208,plain,(
% 0.20/0.43    ~v1_tops_1(sK1,sK0) | v1_subset_1(sK1,k2_struct_0(sK0)) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.43    inference(resolution,[],[f185,f77])).
% 0.20/0.43  fof(f77,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f43])).
% 0.20/0.43  fof(f43,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f42])).
% 0.20/0.43  fof(f42,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f15])).
% 0.20/0.43  fof(f15,axiom,(
% 0.20/0.43    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).
% 0.20/0.43  fof(f185,plain,(
% 0.20/0.43    ~v2_tex_2(sK1,sK0) | ~v1_tops_1(sK1,sK0) | v1_subset_1(sK1,k2_struct_0(sK0))),
% 0.20/0.43    inference(subsumption_resolution,[],[f184,f153])).
% 0.20/0.43  fof(f184,plain,(
% 0.20/0.43    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v1_subset_1(sK1,k2_struct_0(sK0)) | ~v1_tops_1(sK1,sK0) | ~v2_tex_2(sK1,sK0)),
% 0.20/0.43    inference(forward_demodulation,[],[f183,f149])).
% 0.20/0.43  fof(f183,plain,(
% 0.20/0.43    v1_subset_1(sK1,k2_struct_0(sK0)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(sK1,sK0) | ~v2_tex_2(sK1,sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f182,f55])).
% 0.20/0.43  fof(f182,plain,(
% 0.20/0.43    v1_subset_1(sK1,k2_struct_0(sK0)) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(sK1,sK0) | ~v2_tex_2(sK1,sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f181,f53])).
% 0.20/0.43  fof(f181,plain,(
% 0.20/0.43    v1_subset_1(sK1,k2_struct_0(sK0)) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(sK1,sK0) | ~v2_tex_2(sK1,sK0)),
% 0.20/0.43    inference(subsumption_resolution,[],[f180,f52])).
% 0.20/0.43  fof(f180,plain,(
% 0.20/0.43    v1_subset_1(sK1,k2_struct_0(sK0)) | v2_struct_0(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(sK1,sK0) | ~v2_tex_2(sK1,sK0)),
% 0.20/0.43    inference(resolution,[],[f152,f72])).
% 0.20/0.43  fof(f72,plain,(
% 0.20/0.43    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | ~v2_tex_2(X1,X0) | v3_tex_2(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f37])).
% 0.20/0.43  fof(f37,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.43    inference(flattening,[],[f36])).
% 0.20/0.43  fof(f36,plain,(
% 0.20/0.43    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.43    inference(ennf_transformation,[],[f18])).
% 0.20/0.43  fof(f18,axiom,(
% 0.20/0.43    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 0.20/0.43    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_tex_2)).
% 0.20/0.43  fof(f152,plain,(
% 0.20/0.43    ~v3_tex_2(sK1,sK0) | v1_subset_1(sK1,k2_struct_0(sK0))),
% 0.20/0.43    inference(backward_demodulation,[],[f50,f149])).
% 0.20/0.43  fof(f50,plain,(
% 0.20/0.43    v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)),
% 0.20/0.43    inference(cnf_transformation,[],[f22])).
% 0.20/0.43  fof(f361,plain,(
% 0.20/0.43    ~v1_subset_1(sK1,sK1)),
% 0.20/0.43    inference(resolution,[],[f352,f87])).
% 0.20/0.43  fof(f87,plain,(
% 0.20/0.43    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 0.20/0.43    inference(equality_resolution,[],[f84])).
% 0.20/0.43  fof(f84,plain,(
% 0.20/0.43    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 0.20/0.43    inference(cnf_transformation,[],[f48])).
% 0.20/0.43  fof(f352,plain,(
% 0.20/0.43    m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.20/0.43    inference(backward_demodulation,[],[f153,f346])).
% 0.20/0.43  % SZS output end Proof for theBenchmark
% 0.20/0.43  % (21983)------------------------------
% 0.20/0.43  % (21983)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.43  % (21983)Termination reason: Refutation
% 0.20/0.43  
% 0.20/0.43  % (21983)Memory used [KB]: 1791
% 0.20/0.43  % (21983)Time elapsed: 0.014 s
% 0.20/0.43  % (21983)------------------------------
% 0.20/0.43  % (21983)------------------------------
% 0.20/0.43  % (21964)Success in time 0.088 s
%------------------------------------------------------------------------------
