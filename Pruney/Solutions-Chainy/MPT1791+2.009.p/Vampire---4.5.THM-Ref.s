%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:22 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 587 expanded)
%              Number of leaves         :    8 ( 102 expanded)
%              Depth                    :   25
%              Number of atoms          :  286 (2701 expanded)
%              Number of equality atoms :   65 ( 475 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f138,plain,(
    $false ),
    inference(subsumption_resolution,[],[f137,f118])).

fof(f118,plain,(
    ~ v3_pre_topc(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f113])).

fof(f113,plain,
    ( k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f24,f110])).

fof(f110,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f105])).

fof(f105,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(superposition,[],[f104,f86])).

fof(f86,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f85,f25])).

fof(f25,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f10])).

fof(f10,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f8])).

fof(f8,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

fof(f85,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f84,f23])).

fof(f23,plain,
    ( v3_pre_topc(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f11])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_pre_topc(sK0) = k5_tmap_1(sK0,X0) ) ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,(
    ! [X0] :
      ( u1_pre_topc(sK0) = k5_tmap_1(sK0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f82,f55])).

fof(f55,plain,(
    ! [X1] :
      ( r2_hidden(X1,u1_pre_topc(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0) ) ),
    inference(resolution,[],[f28,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f28,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f82,plain,(
    ! [X3] :
      ( ~ r2_hidden(X3,u1_pre_topc(sK0))
      | u1_pre_topc(sK0) = k5_tmap_1(sK0,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f51,f28])).

fof(f51,plain,(
    ! [X3] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_pre_topc(sK0) = k5_tmap_1(sK0,X3)
      | ~ r2_hidden(X3,u1_pre_topc(sK0)) ) ),
    inference(subsumption_resolution,[],[f45,f26])).

fof(f26,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f45,plain,(
    ! [X3] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_pre_topc(sK0) = k5_tmap_1(sK0,X3)
      | ~ r2_hidden(X3,u1_pre_topc(sK0)) ) ),
    inference(resolution,[],[f27,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ r2_hidden(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f27,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f104,plain,(
    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f103,f73])).

fof(f73,plain,(
    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f72,f25])).

fof(f72,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X4)) ) ),
    inference(subsumption_resolution,[],[f52,f28])).

fof(f52,plain,(
    ! [X4] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X4)) ) ),
    inference(subsumption_resolution,[],[f46,f26])).

fof(f46,plain,(
    ! [X4] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X4)) ) ),
    inference(resolution,[],[f27,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f103,plain,(
    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),k5_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f102,f77])).

fof(f77,plain,(
    u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f76,f25])).

fof(f76,plain,(
    ! [X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | k5_tmap_1(sK0,X5) = u1_pre_topc(k6_tmap_1(sK0,X5)) ) ),
    inference(subsumption_resolution,[],[f53,f28])).

fof(f53,plain,(
    ! [X5] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | k5_tmap_1(sK0,X5) = u1_pre_topc(k6_tmap_1(sK0,X5)) ) ),
    inference(subsumption_resolution,[],[f47,f26])).

fof(f47,plain,(
    ! [X5] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
      | k5_tmap_1(sK0,X5) = u1_pre_topc(k6_tmap_1(sK0,X5)) ) ),
    inference(resolution,[],[f27,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f102,plain,(
    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f100,f25])).

fof(f100,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) ) ),
    inference(subsumption_resolution,[],[f57,f66])).

fof(f66,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | l1_pre_topc(k6_tmap_1(sK0,X2)) ) ),
    inference(subsumption_resolution,[],[f50,f28])).

fof(f50,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | l1_pre_topc(k6_tmap_1(sK0,X2)) ) ),
    inference(subsumption_resolution,[],[f44,f26])).

fof(f44,plain,(
    ! [X2] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | l1_pre_topc(k6_tmap_1(sK0,X2)) ) ),
    inference(resolution,[],[f27,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | l1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f57,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(k6_tmap_1(sK0,X0))
      | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0))) ) ),
    inference(resolution,[],[f56,f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f56,plain,(
    ! [X0] :
      ( v1_pre_topc(k6_tmap_1(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f48,f28])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_pre_topc(k6_tmap_1(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f42,f26])).

fof(f42,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_pre_topc(k6_tmap_1(sK0,X0)) ) ),
    inference(resolution,[],[f27,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f24,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f11])).

fof(f137,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f136,f25])).

fof(f136,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f134,f54])).

fof(f54,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X0,sK0) ) ),
    inference(resolution,[],[f28,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f134,plain,(
    r2_hidden(sK1,u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f133,f26])).

fof(f133,plain,
    ( v2_struct_0(sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f132,f25])).

fof(f132,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f131,f28])).

fof(f131,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f130,f27])).

fof(f130,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0)) ),
    inference(trivial_inequality_removal,[],[f129])).

fof(f129,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(sK0)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | r2_hidden(sK1,u1_pre_topc(sK0)) ),
    inference(superposition,[],[f35,f123])).

fof(f123,plain,(
    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    inference(trivial_inequality_removal,[],[f122])).

fof(f122,plain,
    ( k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK1)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    inference(superposition,[],[f112,f110])).

fof(f112,plain,(
    ! [X6,X7] :
      ( k6_tmap_1(sK0,sK1) != g1_pre_topc(X6,X7)
      | k5_tmap_1(sK0,sK1) = X7 ) ),
    inference(subsumption_resolution,[],[f109,f78])).

fof(f78,plain,(
    m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(backward_demodulation,[],[f75,f77])).

fof(f75,plain,(
    m1_subset_1(u1_pre_topc(k6_tmap_1(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f74,f67])).

fof(f67,plain,(
    l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f66,f25])).

fof(f74,plain,
    ( m1_subset_1(u1_pre_topc(k6_tmap_1(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(superposition,[],[f29,f73])).

fof(f29,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f109,plain,(
    ! [X6,X7] :
      ( k6_tmap_1(sK0,sK1) != g1_pre_topc(X6,X7)
      | ~ m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))
      | k5_tmap_1(sK0,sK1) = X7 ) ),
    inference(superposition,[],[f38,f104])).

% (24750)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% (24752)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% (24763)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% (24740)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% (24741)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% (24742)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% (24747)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% (24755)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% (24739)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% (24759)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% (24744)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% (24739)Refutation not found, incomplete strategy% (24739)------------------------------
% (24739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (24739)Termination reason: Refutation not found, incomplete strategy

% (24739)Memory used [KB]: 1791
% (24739)Time elapsed: 0.127 s
% (24739)------------------------------
% (24739)------------------------------
% (24756)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% (24751)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% (24749)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
fof(f38,plain,(
    ! [X2,X0,X3,X1] :
      ( g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
      | X1 = X3 ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2,X3] :
          ( ( X1 = X3
            & X0 = X2 )
          | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0)))
     => ! [X2,X3] :
          ( g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3)
         => ( X1 = X3
            & X0 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).

fof(f35,plain,(
    ! [X0,X1] :
      ( u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | r2_hidden(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f19])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:57:00 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.51  % (24761)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.22/0.51  % (24753)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.22/0.52  % (24768)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.22/0.52  % (24745)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.22/0.52  % (24761)Refutation not found, incomplete strategy% (24761)------------------------------
% 0.22/0.52  % (24761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (24761)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (24761)Memory used [KB]: 10746
% 0.22/0.52  % (24761)Time elapsed: 0.050 s
% 0.22/0.52  % (24761)------------------------------
% 0.22/0.52  % (24761)------------------------------
% 0.22/0.52  % (24760)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.22/0.53  % (24760)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f138,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f137,f118])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    ~v3_pre_topc(sK1,sK0)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f113])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.22/0.53    inference(backward_demodulation,[],[f24,f110])).
% 0.22/0.53  fof(f110,plain,(
% 0.22/0.53    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f105])).
% 0.22/0.53  fof(f105,plain,(
% 0.22/0.53    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 0.22/0.53    inference(superposition,[],[f104,f86])).
% 0.22/0.53  fof(f86,plain,(
% 0.22/0.53    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 0.22/0.53    inference(subsumption_resolution,[],[f85,f25])).
% 0.22/0.53  fof(f25,plain,(
% 0.22/0.53    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f10])).
% 0.22/0.53  fof(f10,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,negated_conjecture,(
% 0.22/0.53    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 0.22/0.53    inference(negated_conjecture,[],[f8])).
% 0.22/0.53  fof(f8,conjecture,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).
% 0.22/0.53  fof(f85,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 0.22/0.53    inference(resolution,[],[f84,f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    v3_pre_topc(sK1,sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f84,plain,(
% 0.22/0.53    ( ! [X0] : (~v3_pre_topc(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X0)) )),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f83])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    ( ! [X0] : (u1_pre_topc(sK0) = k5_tmap_1(sK0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X0,sK0)) )),
% 0.22/0.53    inference(resolution,[],[f82,f55])).
% 0.22/0.53  fof(f55,plain,(
% 0.22/0.53    ( ! [X1] : (r2_hidden(X1,u1_pre_topc(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0)) )),
% 0.22/0.53    inference(resolution,[],[f28,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f82,plain,(
% 0.22/0.53    ( ! [X3] : (~r2_hidden(X3,u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f51,f28])).
% 0.22/0.53  fof(f51,plain,(
% 0.22/0.53    ( ! [X3] : (~l1_pre_topc(sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X3) | ~r2_hidden(X3,u1_pre_topc(sK0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f45,f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ~v2_struct_0(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f45,plain,(
% 0.22/0.53    ( ! [X3] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X3) | ~r2_hidden(X3,u1_pre_topc(sK0))) )),
% 0.22/0.53    inference(resolution,[],[f27,f36])).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).
% 0.22/0.53  fof(f27,plain,(
% 0.22/0.53    v2_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f104,plain,(
% 0.22/0.53    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),k5_tmap_1(sK0,sK1))),
% 0.22/0.53    inference(forward_demodulation,[],[f103,f73])).
% 0.22/0.53  fof(f73,plain,(
% 0.22/0.53    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,sK1))),
% 0.22/0.53    inference(resolution,[],[f72,f25])).
% 0.22/0.53  fof(f72,plain,(
% 0.22/0.53    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X4))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f52,f28])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X4] : (~l1_pre_topc(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X4))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f46,f26])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X4] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X4))) )),
% 0.22/0.53    inference(resolution,[],[f27,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f7])).
% 0.22/0.53  fof(f7,axiom,(
% 0.22/0.53    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).
% 0.22/0.53  fof(f103,plain,(
% 0.22/0.53    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),k5_tmap_1(sK0,sK1))),
% 0.22/0.53    inference(forward_demodulation,[],[f102,f77])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1)),
% 0.22/0.53    inference(resolution,[],[f76,f25])).
% 0.22/0.53  fof(f76,plain,(
% 0.22/0.53    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | k5_tmap_1(sK0,X5) = u1_pre_topc(k6_tmap_1(sK0,X5))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f53,f28])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X5] : (~l1_pre_topc(sK0) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | k5_tmap_1(sK0,X5) = u1_pre_topc(k6_tmap_1(sK0,X5))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f47,f26])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X5] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | k5_tmap_1(sK0,X5) = u1_pre_topc(k6_tmap_1(sK0,X5))) )),
% 0.22/0.53    inference(resolution,[],[f27,f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f102,plain,(
% 0.22/0.53    k6_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_pre_topc(k6_tmap_1(sK0,sK1)))),
% 0.22/0.53    inference(resolution,[],[f100,f25])).
% 0.22/0.53  fof(f100,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0)))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f57,f66])).
% 0.22/0.53  fof(f66,plain,(
% 0.22/0.53    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | l1_pre_topc(k6_tmap_1(sK0,X2))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f50,f28])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X2] : (~l1_pre_topc(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | l1_pre_topc(k6_tmap_1(sK0,X2))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f44,f26])).
% 0.22/0.53  fof(f44,plain,(
% 0.22/0.53    ( ! [X2] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | l1_pre_topc(k6_tmap_1(sK0,X2))) )),
% 0.22/0.53    inference(resolution,[],[f27,f41])).
% 0.22/0.53  fof(f41,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | l1_pre_topc(k6_tmap_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f22,plain,(
% 0.22/0.53    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.22/0.53    inference(flattening,[],[f21])).
% 0.22/0.53  fof(f21,plain,(
% 0.22/0.53    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.22/0.53    inference(ennf_transformation,[],[f5])).
% 0.22/0.53  fof(f5,axiom,(
% 0.22/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(k6_tmap_1(sK0,X0)) | k6_tmap_1(sK0,X0) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,X0)),u1_pre_topc(k6_tmap_1(sK0,X0)))) )),
% 0.22/0.53    inference(resolution,[],[f56,f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ( ! [X0] : (~v1_pre_topc(X0) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0) )),
% 0.22/0.53    inference(cnf_transformation,[],[f14])).
% 0.22/0.53  fof(f14,plain,(
% 0.22/0.53    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f13])).
% 0.22/0.53  fof(f13,plain,(
% 0.22/0.53    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.22/0.53  fof(f56,plain,(
% 0.22/0.53    ( ! [X0] : (v1_pre_topc(k6_tmap_1(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f48,f28])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_pre_topc(k6_tmap_1(sK0,X0))) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f42,f26])).
% 0.22/0.53  fof(f42,plain,(
% 0.22/0.53    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_pre_topc(k6_tmap_1(sK0,X0))) )),
% 0.22/0.53    inference(resolution,[],[f27,f39])).
% 0.22/0.53  fof(f39,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_pre_topc(k6_tmap_1(X0,X1))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f22])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,sK1) | ~v3_pre_topc(sK1,sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f11])).
% 0.22/0.53  fof(f137,plain,(
% 0.22/0.53    v3_pre_topc(sK1,sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f136,f25])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,sK0)),
% 0.22/0.53    inference(resolution,[],[f134,f54])).
% 0.22/0.53  fof(f54,plain,(
% 0.22/0.53    ( ! [X0] : (~r2_hidden(X0,u1_pre_topc(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X0,sK0)) )),
% 0.22/0.53    inference(resolution,[],[f28,f31])).
% 0.22/0.53  fof(f31,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f15])).
% 0.22/0.53  fof(f134,plain,(
% 0.22/0.53    r2_hidden(sK1,u1_pre_topc(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f133,f26])).
% 0.22/0.53  fof(f133,plain,(
% 0.22/0.53    v2_struct_0(sK0) | r2_hidden(sK1,u1_pre_topc(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f132,f25])).
% 0.22/0.53  fof(f132,plain,(
% 0.22/0.53    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | r2_hidden(sK1,u1_pre_topc(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f131,f28])).
% 0.22/0.53  fof(f131,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | r2_hidden(sK1,u1_pre_topc(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f130,f27])).
% 0.22/0.53  fof(f130,plain,(
% 0.22/0.53    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | r2_hidden(sK1,u1_pre_topc(sK0))),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f129])).
% 0.22/0.53  fof(f129,plain,(
% 0.22/0.53    u1_pre_topc(sK0) != u1_pre_topc(sK0) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | r2_hidden(sK1,u1_pre_topc(sK0))),
% 0.22/0.53    inference(superposition,[],[f35,f123])).
% 0.22/0.53  fof(f123,plain,(
% 0.22/0.53    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 0.22/0.53    inference(trivial_inequality_removal,[],[f122])).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    k6_tmap_1(sK0,sK1) != k6_tmap_1(sK0,sK1) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 0.22/0.53    inference(superposition,[],[f112,f110])).
% 0.22/0.53  fof(f112,plain,(
% 0.22/0.53    ( ! [X6,X7] : (k6_tmap_1(sK0,sK1) != g1_pre_topc(X6,X7) | k5_tmap_1(sK0,sK1) = X7) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f109,f78])).
% 0.22/0.53  fof(f78,plain,(
% 0.22/0.53    m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.53    inference(backward_demodulation,[],[f75,f77])).
% 0.22/0.53  fof(f75,plain,(
% 0.22/0.53    m1_subset_1(u1_pre_topc(k6_tmap_1(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.53    inference(subsumption_resolution,[],[f74,f67])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.22/0.53    inference(resolution,[],[f66,f25])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    m1_subset_1(u1_pre_topc(k6_tmap_1(sK0,sK1)),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | ~l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 0.22/0.53    inference(superposition,[],[f29,f73])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ( ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,plain,(
% 0.22/0.53    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.22/0.53  fof(f109,plain,(
% 0.22/0.53    ( ! [X6,X7] : (k6_tmap_1(sK0,sK1) != g1_pre_topc(X6,X7) | ~m1_subset_1(k5_tmap_1(sK0,sK1),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) | k5_tmap_1(sK0,sK1) = X7) )),
% 0.22/0.53    inference(superposition,[],[f38,f104])).
% 0.22/0.53  % (24750)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.22/0.53  % (24752)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.22/0.53  % (24763)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.22/0.54  % (24740)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.22/0.54  % (24741)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.54  % (24742)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.22/0.54  % (24747)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.22/0.54  % (24755)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.22/0.54  % (24739)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.22/0.54  % (24759)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.22/0.54  % (24744)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.22/0.55  % (24739)Refutation not found, incomplete strategy% (24739)------------------------------
% 0.22/0.55  % (24739)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (24739)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (24739)Memory used [KB]: 1791
% 0.22/0.55  % (24739)Time elapsed: 0.127 s
% 0.22/0.55  % (24739)------------------------------
% 0.22/0.55  % (24739)------------------------------
% 0.22/0.55  % (24756)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.22/0.55  % (24751)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (24749)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.22/0.55  fof(f38,plain,(
% 0.22/0.55    ( ! [X2,X0,X3,X1] : (g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) | X1 = X3) )),
% 0.22/0.55    inference(cnf_transformation,[],[f20])).
% 0.22/0.55  fof(f20,plain,(
% 0.22/0.55    ! [X0,X1] : (! [X2,X3] : ((X1 = X3 & X0 = X2) | g1_pre_topc(X0,X1) != g1_pre_topc(X2,X3)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))))),
% 0.22/0.55    inference(ennf_transformation,[],[f4])).
% 0.22/0.55  fof(f4,axiom,(
% 0.22/0.55    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(k1_zfmisc_1(X0))) => ! [X2,X3] : (g1_pre_topc(X0,X1) = g1_pre_topc(X2,X3) => (X1 = X3 & X0 = X2)))),
% 0.22/0.55    file('/export/starexec/sandbox/benchmark/theBenchmark.p',free_g1_pre_topc)).
% 0.22/0.55  fof(f35,plain,(
% 0.22/0.55    ( ! [X0,X1] : (u1_pre_topc(X0) != k5_tmap_1(X0,X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | r2_hidden(X1,u1_pre_topc(X0))) )),
% 0.22/0.55    inference(cnf_transformation,[],[f19])).
% 0.22/0.55  % SZS output end Proof for theBenchmark
% 0.22/0.55  % (24760)------------------------------
% 0.22/0.55  % (24760)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (24760)Termination reason: Refutation
% 0.22/0.55  
% 0.22/0.55  % (24760)Memory used [KB]: 1791
% 0.22/0.55  % (24760)Time elapsed: 0.110 s
% 0.22/0.55  % (24760)------------------------------
% 0.22/0.55  % (24760)------------------------------
% 0.22/0.55  % (24738)Success in time 0.18 s
%------------------------------------------------------------------------------
