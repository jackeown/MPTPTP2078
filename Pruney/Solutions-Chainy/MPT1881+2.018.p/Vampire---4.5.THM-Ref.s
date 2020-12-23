%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:55 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   99 ( 529 expanded)
%              Number of leaves         :   14 ( 110 expanded)
%              Depth                    :   17
%              Number of atoms          :  331 (2071 expanded)
%              Number of equality atoms :   39 ( 138 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f252,plain,(
    $false ),
    inference(subsumption_resolution,[],[f215,f247])).

fof(f247,plain,(
    ~ v1_tops_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f179,f246])).

fof(f246,plain,(
    ~ v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f202,f66])).

fof(f66,plain,(
    ! [X1] : ~ v1_subset_1(X1,X1) ),
    inference(subsumption_resolution,[],[f63,f64])).

fof(f64,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f42,f41])).

fof(f41,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).

fof(f42,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f63,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X1))
      | ~ v1_subset_1(X1,X1) ) ),
    inference(equality_resolution,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f202,plain,
    ( v1_subset_1(sK1,sK1)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(backward_demodulation,[],[f72,f199])).

fof(f199,plain,(
    sK1 = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f197,f83])).

fof(f83,plain,
    ( v3_tex_2(sK1,sK0)
    | sK1 = k2_struct_0(sK0) ),
    inference(resolution,[],[f82,f71])).

fof(f71,plain,
    ( ~ v1_subset_1(sK1,k2_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(backward_demodulation,[],[f34,f70])).

fof(f70,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f43,f67])).

fof(f67,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f44,f40])).

fof(f40,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_tex_2(X1,X0)
          <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).

fof(f44,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f43,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f34,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f82,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | sK1 = k2_struct_0(sK0) ),
    inference(resolution,[],[f59,f73])).

fof(f73,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f36,f70])).

fof(f36,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f197,plain,
    ( sK1 = k2_struct_0(sK0)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f194,f73])).

fof(f194,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_struct_0(sK0) = X0
      | ~ v3_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f190,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f190,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X0,k2_struct_0(sK0))
      | k2_struct_0(sK0) = X0
      | ~ v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f189,f64])).

fof(f189,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ v3_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f188,f96])).

fof(f96,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_tex_2(X0,sK0) ) ),
    inference(forward_demodulation,[],[f95,f70])).

fof(f95,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f94,f40])).

fof(f94,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f93,f37])).

fof(f37,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f93,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f65,f39])).

fof(f39,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v1_tdlat_3(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(subsumption_resolution,[],[f56,f45])).

fof(f45,plain,(
    ! [X0] :
      ( ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_tdlat_3(X0)
       => v2_pre_topc(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).

fof(f56,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).

fof(f188,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_tex_2(X1,sK0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ v3_tex_2(X0,sK0) ) ),
    inference(forward_demodulation,[],[f187,f70])).

fof(f187,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X1,sK0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ v3_tex_2(X0,sK0) ) ),
    inference(forward_demodulation,[],[f186,f70])).

fof(f186,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X1,sK0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1
      | ~ v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f54,f40])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X2,X0)
      | ~ r1_tarski(X1,X2)
      | X1 = X2
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).

fof(f72,plain,
    ( v1_subset_1(sK1,k2_struct_0(sK0))
    | ~ v3_tex_2(sK1,sK0) ),
    inference(backward_demodulation,[],[f35,f70])).

fof(f35,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f179,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ v1_tops_1(sK1,sK0) ),
    inference(resolution,[],[f176,f73])).

fof(f176,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_tops_1(X0,sK0)
      | v3_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f175,f96])).

fof(f175,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v1_tops_1(X0,sK0)
      | ~ v2_tex_2(X0,sK0)
      | v3_tex_2(X0,sK0) ) ),
    inference(forward_demodulation,[],[f174,f70])).

fof(f174,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_tops_1(X0,sK0)
      | ~ v2_tex_2(X0,sK0)
      | v3_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f173,f40])).

fof(f173,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_tops_1(X0,sK0)
      | ~ v2_tex_2(X0,sK0)
      | v3_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f172,f37])).

fof(f172,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_tops_1(X0,sK0)
      | ~ v2_tex_2(X0,sK0)
      | v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f57,f38])).

fof(f38,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_tops_1(X1,X0)
      | ~ v2_tex_2(X1,X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v3_tex_2(X1,X0)
          | ~ v2_tex_2(X1,X0)
          | ~ v1_tops_1(X1,X0)
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
         => ( ( v2_tex_2(X1,X0)
              & v1_tops_1(X1,X0) )
           => v3_tex_2(X1,X0) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).

fof(f215,plain,(
    v1_tops_1(sK1,sK0) ),
    inference(backward_demodulation,[],[f114,f199])).

fof(f114,plain,(
    v1_tops_1(k2_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f113,f64])).

fof(f113,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0)))
    | v1_tops_1(k2_struct_0(sK0),sK0) ),
    inference(forward_demodulation,[],[f112,f70])).

fof(f112,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_tops_1(k2_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f111,f40])).

fof(f111,plain,
    ( ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(k2_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f110,f70])).

fof(f110,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | ~ m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v1_tops_1(k2_struct_0(sK0),sK0) ),
    inference(superposition,[],[f48,f107])).

fof(f107,plain,(
    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f104,f79])).

fof(f79,plain,(
    v4_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f78,f40])).

fof(f78,plain,
    ( ~ l1_pre_topc(sK0)
    | v4_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(resolution,[],[f58,f38])).

fof(f58,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v4_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( v4_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v4_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).

fof(f104,plain,
    ( ~ v4_pre_topc(k2_struct_0(sK0),sK0)
    | k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0)) ),
    inference(resolution,[],[f103,f64])).

fof(f103,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0)
      | k2_pre_topc(sK0,X0) = X0 ) ),
    inference(forward_demodulation,[],[f102,f70])).

fof(f102,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v4_pre_topc(X0,sK0)
      | k2_pre_topc(sK0,X0) = X0 ) ),
    inference(resolution,[],[f47,f40])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v4_pre_topc(X1,X0)
      | k2_pre_topc(X0,X1) = X1 ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ( v4_pre_topc(X1,X0)
              | k2_pre_topc(X0,X1) != X1
              | ~ v2_pre_topc(X0) )
            & ( k2_pre_topc(X0,X1) = X1
              | ~ v4_pre_topc(X1,X0) ) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( ( ( k2_pre_topc(X0,X1) = X1
                & v2_pre_topc(X0) )
             => v4_pre_topc(X1,X0) )
            & ( v4_pre_topc(X1,X0)
             => k2_pre_topc(X0,X1) = X1 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).

fof(f48,plain,(
    ! [X0,X1] :
      ( u1_struct_0(X0) != k2_pre_topc(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v1_tops_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v1_tops_1(X1,X0)
          <=> u1_struct_0(X0) = k2_pre_topc(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 10:26:35 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.49  % (31826)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.49  % (31841)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.49  % (31840)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.49  % (31832)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (31845)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.50  % (31833)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.50  % (31825)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (31833)Refutation not found, incomplete strategy% (31833)------------------------------
% 0.21/0.50  % (31833)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (31833)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (31833)Memory used [KB]: 10618
% 0.21/0.50  % (31833)Time elapsed: 0.081 s
% 0.21/0.50  % (31833)------------------------------
% 0.21/0.50  % (31833)------------------------------
% 0.21/0.50  % (31823)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (31842)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.50  % (31827)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % (31841)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f252,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f215,f247])).
% 0.21/0.50  fof(f247,plain,(
% 0.21/0.50    ~v1_tops_1(sK1,sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f179,f246])).
% 0.21/0.50  fof(f246,plain,(
% 0.21/0.50    ~v3_tex_2(sK1,sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f202,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X1] : (~v1_subset_1(X1,X1)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f63,f64])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f42,f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(X1)) | ~v1_subset_1(X1,X1)) )),
% 0.21/0.50    inference(equality_resolution,[],[f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    v1_subset_1(sK1,sK1) | ~v3_tex_2(sK1,sK0)),
% 0.21/0.50    inference(backward_demodulation,[],[f72,f199])).
% 0.21/0.50  fof(f199,plain,(
% 0.21/0.50    sK1 = k2_struct_0(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f197,f83])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    v3_tex_2(sK1,sK0) | sK1 = k2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f82,f71])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ~v1_subset_1(sK1,k2_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 0.21/0.50    inference(backward_demodulation,[],[f34,f70])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f43,f67])).
% 0.21/0.50  fof(f67,plain,(
% 0.21/0.50    l1_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f44,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f16])).
% 0.21/0.50  fof(f16,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f15])).
% 0.21/0.50  fof(f15,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f14])).
% 0.21/0.50  fof(f14,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_tex_2)).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    v1_subset_1(sK1,k2_struct_0(sK0)) | sK1 = k2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f59,f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 0.21/0.50    inference(backward_demodulation,[],[f36,f70])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f33])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    sK1 = k2_struct_0(sK0) | ~v3_tex_2(sK1,sK0)),
% 0.21/0.50    inference(resolution,[],[f194,f73])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = X0 | ~v3_tex_2(X0,sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f190,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.50  fof(f190,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,k2_struct_0(sK0)) | k2_struct_0(sK0) = X0 | ~v3_tex_2(X0,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f189,f64])).
% 0.21/0.50  fof(f189,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~r1_tarski(X0,X1) | X0 = X1 | ~v3_tex_2(X0,sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f188,f96])).
% 0.21/0.50  fof(f96,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v2_tex_2(X0,sK0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f95,f70])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f94,f40])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f93,f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f65,f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    v1_tdlat_3(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f17])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_tdlat_3(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f56,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_pre_topc(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : ((v2_pre_topc(X0) | ~v1_tdlat_3(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => (v1_tdlat_3(X0) => v2_pre_topc(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tdlat_3)).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_tex_2)).
% 0.21/0.50  fof(f188,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~r1_tarski(X0,X1) | X0 = X1 | ~v3_tex_2(X0,sK0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f187,f70])).
% 0.21/0.50  fof(f187,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~r1_tarski(X0,X1) | X0 = X1 | ~v3_tex_2(X0,sK0)) )),
% 0.21/0.50    inference(forward_demodulation,[],[f186,f70])).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X1,sK0) | ~r1_tarski(X0,X1) | X0 = X1 | ~v3_tex_2(X0,sK0)) )),
% 0.21/0.50    inference(resolution,[],[f54,f40])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X2,X0) | ~r1_tarski(X1,X2) | X1 = X2 | ~v3_tex_2(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    v1_subset_1(sK1,k2_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)),
% 0.21/0.50    inference(backward_demodulation,[],[f35,f70])).
% 0.21/0.51  fof(f35,plain,(
% 0.21/0.51    v1_subset_1(sK1,u1_struct_0(sK0)) | ~v3_tex_2(sK1,sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    v3_tex_2(sK1,sK0) | ~v1_tops_1(sK1,sK0)),
% 0.21/0.51    inference(resolution,[],[f176,f73])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | v3_tex_2(X0,sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f175,f96])).
% 0.21/0.51  fof(f175,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | ~v2_tex_2(X0,sK0) | v3_tex_2(X0,sK0)) )),
% 0.21/0.51    inference(forward_demodulation,[],[f174,f70])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | ~v2_tex_2(X0,sK0) | v3_tex_2(X0,sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f173,f40])).
% 0.21/0.51  fof(f173,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | ~v2_tex_2(X0,sK0) | v3_tex_2(X0,sK0)) )),
% 0.21/0.51    inference(subsumption_resolution,[],[f172,f37])).
% 0.21/0.51  fof(f172,plain,(
% 0.21/0.51    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_tops_1(X0,sK0) | ~v2_tex_2(X0,sK0) | v3_tex_2(X0,sK0)) )),
% 0.21/0.51    inference(resolution,[],[f57,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    v2_pre_topc(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f17])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_tops_1(X1,X0) | ~v2_tex_2(X1,X0) | v3_tex_2(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (v3_tex_2(X1,X0) | ~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) | (~v2_tex_2(X1,X0) | ~v1_tops_1(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_tex_2(X1,X0) & v1_tops_1(X1,X0)) => v3_tex_2(X1,X0))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_tex_2)).
% 0.21/0.51  fof(f215,plain,(
% 0.21/0.51    v1_tops_1(sK1,sK0)),
% 0.21/0.51    inference(backward_demodulation,[],[f114,f199])).
% 0.21/0.51  fof(f114,plain,(
% 0.21/0.51    v1_tops_1(k2_struct_0(sK0),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f113,f64])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(k2_struct_0(sK0))) | v1_tops_1(k2_struct_0(sK0),sK0)),
% 0.21/0.51    inference(forward_demodulation,[],[f112,f70])).
% 0.21/0.51  fof(f112,plain,(
% 0.21/0.51    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_tops_1(k2_struct_0(sK0),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f111,f40])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v1_tops_1(k2_struct_0(sK0),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f110,f70])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    u1_struct_0(sK0) != k2_struct_0(sK0) | ~m1_subset_1(k2_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v1_tops_1(k2_struct_0(sK0),sK0)),
% 0.21/0.51    inference(superposition,[],[f48,f107])).
% 0.21/0.51  fof(f107,plain,(
% 0.21/0.51    k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))),
% 0.21/0.51    inference(subsumption_resolution,[],[f104,f79])).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    v4_pre_topc(k2_struct_0(sK0),sK0)),
% 0.21/0.51    inference(subsumption_resolution,[],[f78,f40])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ~l1_pre_topc(sK0) | v4_pre_topc(k2_struct_0(sK0),sK0)),
% 0.21/0.51    inference(resolution,[],[f58,f38])).
% 0.21/0.51  fof(f58,plain,(
% 0.21/0.51    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v4_pre_topc(k2_struct_0(X0),X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0] : (v4_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v4_pre_topc(k2_struct_0(X0),X0))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_pre_topc)).
% 0.21/0.51  fof(f104,plain,(
% 0.21/0.51    ~v4_pre_topc(k2_struct_0(sK0),sK0) | k2_struct_0(sK0) = k2_pre_topc(sK0,k2_struct_0(sK0))),
% 0.21/0.51    inference(resolution,[],[f103,f64])).
% 0.21/0.51  fof(f103,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | k2_pre_topc(sK0,X0) = X0) )),
% 0.21/0.51    inference(forward_demodulation,[],[f102,f70])).
% 0.21/0.51  fof(f102,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v4_pre_topc(X0,sK0) | k2_pre_topc(sK0,X0) = X0) )),
% 0.21/0.51    inference(resolution,[],[f47,f40])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) = X1) )),
% 0.21/0.51    inference(cnf_transformation,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0)) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(flattening,[],[f22])).
% 0.21/0.51  fof(f22,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : (((v4_pre_topc(X1,X0) | (k2_pre_topc(X0,X1) != X1 | ~v2_pre_topc(X0))) & (k2_pre_topc(X0,X1) = X1 | ~v4_pre_topc(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (((k2_pre_topc(X0,X1) = X1 & v2_pre_topc(X0)) => v4_pre_topc(X1,X0)) & (v4_pre_topc(X1,X0) => k2_pre_topc(X0,X1) = X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_pre_topc)).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ( ! [X0,X1] : (u1_struct_0(X0) != k2_pre_topc(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v1_tops_1(X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (! [X1] : ((v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v1_tops_1(X1,X0) <=> u1_struct_0(X0) = k2_pre_topc(X0,X1))))),
% 0.21/0.51    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tops_3)).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (31841)------------------------------
% 0.21/0.51  % (31841)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (31841)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (31841)Memory used [KB]: 1791
% 0.21/0.51  % (31841)Time elapsed: 0.091 s
% 0.21/0.51  % (31841)------------------------------
% 0.21/0.51  % (31841)------------------------------
% 0.21/0.51  % (31821)Success in time 0.138 s
%------------------------------------------------------------------------------
