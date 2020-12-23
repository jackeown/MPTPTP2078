%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:21:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  113 (1474 expanded)
%              Number of leaves         :   10 ( 278 expanded)
%              Depth                    :   36
%              Number of atoms          :  365 (7018 expanded)
%              Number of equality atoms :   39 ( 197 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f854,plain,(
    $false ),
    inference(subsumption_resolution,[],[f853,f167])).

fof(f167,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f166,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f166,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | r1_tarski(sK1,sK1) ),
    inference(subsumption_resolution,[],[f165,f28])).

fof(f28,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

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
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
          <~> ~ v1_subset_1(X1,u1_struct_0(X0)) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v1_tdlat_3(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v1_tdlat_3(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_tex_2(X1,X0)
            <=> ~ v1_subset_1(X1,u1_struct_0(X0)) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f165,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,sK1) ),
    inference(duplicate_literal_removal,[],[f163])).

fof(f163,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,sK1) ),
    inference(resolution,[],[f157,f50])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK4(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r1_tarski(X1,X2)
          | ? [X3] :
              ( ~ r2_hidden(X3,X2)
              & r2_hidden(X3,X1)
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                 => r2_hidden(X3,X2) ) )
           => r1_tarski(X1,X2) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).

fof(f157,plain,
    ( r2_hidden(sK4(u1_struct_0(sK0),sK1,sK1),sK1)
    | m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f155,f46])).

fof(f155,plain,
    ( r1_tarski(sK1,sK1)
    | r2_hidden(sK4(u1_struct_0(sK0),sK1,sK1),sK1) ),
    inference(resolution,[],[f59,f28])).

fof(f59,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | r2_hidden(sK4(u1_struct_0(sK0),sK1,X1),sK1)
      | r1_tarski(sK1,X1) ) ),
    inference(resolution,[],[f28,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(sK4(X0,X1,X2),X1)
      | r1_tarski(X1,X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f853,plain,(
    ~ m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f849,f53])).

fof(f53,plain,(
    ! [X1] :
      ( ~ v1_subset_1(X1,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X1)) ) ),
    inference(equality_resolution,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 != X1
      | ~ v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0,X1] :
      ( ( v1_subset_1(X1,X0)
      <=> X0 != X1 )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ( v1_subset_1(X1,X0)
      <=> X0 != X1 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).

fof(f849,plain,(
    v1_subset_1(sK1,sK1) ),
    inference(resolution,[],[f772,f231])).

fof(f231,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | v1_subset_1(sK1,sK1) ),
    inference(backward_demodulation,[],[f27,f229])).

fof(f229,plain,(
    sK1 = u1_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f226,f28])).

fof(f226,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(duplicate_literal_removal,[],[f221])).

fof(f221,plain,
    ( sK1 = u1_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f112,f96])).

fof(f96,plain,
    ( v3_tex_2(sK1,sK0)
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f63,f26])).

fof(f26,plain,
    ( ~ v1_subset_1(sK1,u1_struct_0(sK0))
    | v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f63,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | sK1 = u1_struct_0(sK0) ),
    inference(resolution,[],[f28,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f112,plain,(
    ! [X0] :
      ( ~ v3_tex_2(X0,sK0)
      | u1_struct_0(sK0) = X0
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f111,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f111,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ r1_tarski(X0,u1_struct_0(sK0))
      | u1_struct_0(sK0) = X0
      | ~ v3_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f110,f32])).

fof(f32,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f110,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ r1_tarski(X0,u1_struct_0(sK0))
      | u1_struct_0(sK0) = X0
      | ~ v3_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f101,f56])).

fof(f56,plain,(
    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f55,f32])).

fof(f55,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f54,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f54,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(resolution,[],[f32,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f101,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ r1_tarski(X0,u1_struct_0(sK0))
      | u1_struct_0(sK0) = X0
      | ~ v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f94,f39])).

fof(f39,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_tex_2(X2,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r1_tarski(X1,X2)
      | X1 = X2
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    inference(flattening,[],[f15])).

fof(f15,plain,(
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

fof(f94,plain,(
    v2_tex_2(u1_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f93,f29])).

fof(f29,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f93,plain,
    ( v2_struct_0(sK0)
    | v2_tex_2(u1_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f92,f32])).

fof(f92,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(u1_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f91,f31])).

fof(f31,plain,(
    v1_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f91,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(u1_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f84,f30])).

fof(f30,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f84,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(u1_struct_0(sK0),sK0) ),
    inference(resolution,[],[f56,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v1_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v1_tdlat_3(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).

fof(f27,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | v1_subset_1(sK1,u1_struct_0(sK0)) ),
    inference(cnf_transformation,[],[f13])).

fof(f772,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f645])).

fof(f645,plain,
    ( sK1 != sK1
    | v3_tex_2(sK1,sK0) ),
    inference(backward_demodulation,[],[f80,f642])).

fof(f642,plain,(
    sK1 = sK2(sK0,sK1) ),
    inference(subsumption_resolution,[],[f641,f557])).

fof(f557,plain,
    ( r2_hidden(sK3(sK1,sK1,sK2(sK0,sK1)),sK1)
    | sK1 = sK2(sK0,sK1) ),
    inference(resolution,[],[f177,f329])).

fof(f329,plain,(
    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1)) ),
    inference(subsumption_resolution,[],[f328,f167])).

fof(f328,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f290,f53])).

fof(f290,plain,
    ( v1_subset_1(sK1,sK1)
    | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1)) ),
    inference(forward_demodulation,[],[f256,f229])).

fof(f256,plain,
    ( v1_subset_1(sK1,sK1)
    | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f134,f229])).

fof(f134,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f74,f27])).

fof(f74,plain,
    ( v3_tex_2(sK1,sK0)
    | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f73,f32])).

fof(f73,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f68,f28])).

fof(f68,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f67,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f67,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f66,f29])).

fof(f66,plain,
    ( v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f65,f32])).

fof(f65,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f64,f31])).

fof(f64,plain,
    ( ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f57,f30])).

fof(f57,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v1_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f28,f41])).

fof(f177,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
      | r2_hidden(sK3(sK1,sK1,X2),sK1)
      | sK1 = X2 ) ),
    inference(subsumption_resolution,[],[f174,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X2,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | r2_hidden(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( r2_hidden(X2,X0)
          | ~ r2_hidden(X2,X1) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( r2_hidden(X2,X1)
         => r2_hidden(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).

fof(f174,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(sK1))
      | r2_hidden(sK3(sK1,sK1,X2),X2)
      | r2_hidden(sK3(sK1,sK1,X2),sK1)
      | sK1 = X2 ) ),
    inference(resolution,[],[f167,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | r2_hidden(sK3(X0,X1,X2),X2)
      | r2_hidden(sK3(X0,X1,X2),X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( X1 = X2
          | ? [X3] :
              ( ( r2_hidden(X3,X1)
              <~> r2_hidden(X3,X2) )
              & m1_subset_1(X3,X0) )
          | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(X0))
         => ( ! [X3] :
                ( m1_subset_1(X3,X0)
               => ( r2_hidden(X3,X1)
                <=> r2_hidden(X3,X2) ) )
           => X1 = X2 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).

fof(f641,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ r2_hidden(sK3(sK1,sK1,sK2(sK0,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f640,f167])).

fof(f640,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ r2_hidden(sK3(sK1,sK1,sK2(sK0,sK1)),sK1) ),
    inference(subsumption_resolution,[],[f639,f329])).

fof(f639,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ r2_hidden(sK3(sK1,sK1,sK2(sK0,sK1)),sK1) ),
    inference(duplicate_literal_removal,[],[f637])).

fof(f637,plain,
    ( sK1 = sK2(sK0,sK1)
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ r2_hidden(sK3(sK1,sK1,sK2(sK0,sK1)),sK1)
    | sK1 = sK2(sK0,sK1) ),
    inference(resolution,[],[f635,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(sK3(X0,X1,X2),X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ r2_hidden(sK3(X0,X1,X2),X1)
      | X1 = X2 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f635,plain,
    ( r2_hidden(sK3(sK1,sK1,sK2(sK0,sK1)),sK2(sK0,sK1))
    | sK1 = sK2(sK0,sK1) ),
    inference(resolution,[],[f589,f326])).

fof(f326,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK2(sK0,sK1))) ),
    inference(resolution,[],[f322,f46])).

fof(f322,plain,(
    r1_tarski(sK1,sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f321,f167])).

fof(f321,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    inference(resolution,[],[f255,f53])).

fof(f255,plain,
    ( v1_subset_1(sK1,sK1)
    | r1_tarski(sK1,sK2(sK0,sK1)) ),
    inference(backward_demodulation,[],[f131,f229])).

fof(f131,plain,
    ( v1_subset_1(sK1,u1_struct_0(sK0))
    | r1_tarski(sK1,sK2(sK0,sK1)) ),
    inference(resolution,[],[f78,f27])).

fof(f78,plain,
    ( v3_tex_2(sK1,sK0)
    | r1_tarski(sK1,sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f77,f32])).

fof(f77,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(sK1,sK2(sK0,sK1))
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f70,f28])).

fof(f70,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | r1_tarski(sK1,sK2(sK0,sK1))
    | v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f67,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(X1,sK2(X0,X1))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f589,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(X0))
      | sK1 = sK2(sK0,sK1)
      | r2_hidden(sK3(sK1,sK1,sK2(sK0,sK1)),X0) ) ),
    inference(resolution,[],[f557,f52])).

fof(f80,plain,
    ( sK1 != sK2(sK0,sK1)
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f79,f32])).

fof(f79,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 != sK2(sK0,sK1)
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f71,f28])).

fof(f71,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | sK1 != sK2(sK0,sK1)
    | v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f67,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | sK2(X0,X1) != X1
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 14:07:17 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.52  % (17279)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.53  % (17269)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.53  % (17271)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.54  % (17278)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.54  % (17278)Refutation not found, incomplete strategy% (17278)------------------------------
% 0.21/0.54  % (17278)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (17278)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (17278)Memory used [KB]: 6268
% 0.21/0.54  % (17278)Time elapsed: 0.115 s
% 0.21/0.54  % (17278)------------------------------
% 0.21/0.54  % (17278)------------------------------
% 0.21/0.54  % (17271)Refutation not found, incomplete strategy% (17271)------------------------------
% 0.21/0.54  % (17271)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.55  % (17271)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.55  
% 0.21/0.55  % (17271)Memory used [KB]: 10618
% 0.21/0.55  % (17271)Time elapsed: 0.106 s
% 0.21/0.55  % (17271)------------------------------
% 0.21/0.55  % (17271)------------------------------
% 0.21/0.55  % (17270)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.55  % (17272)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.56  % (17272)Refutation not found, incomplete strategy% (17272)------------------------------
% 0.21/0.56  % (17272)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (17272)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (17272)Memory used [KB]: 1663
% 0.21/0.56  % (17272)Time elapsed: 0.081 s
% 0.21/0.56  % (17272)------------------------------
% 0.21/0.56  % (17272)------------------------------
% 0.21/0.56  % (17265)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.56  % (17288)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.56  % (17266)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.56  % (17265)Refutation not found, incomplete strategy% (17265)------------------------------
% 0.21/0.56  % (17265)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.56  % (17265)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.56  
% 0.21/0.56  % (17265)Memory used [KB]: 10618
% 0.21/0.56  % (17265)Time elapsed: 0.131 s
% 0.21/0.56  % (17265)------------------------------
% 0.21/0.56  % (17265)------------------------------
% 0.21/0.56  % (17284)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.56  % (17281)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.57  % (17277)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.57  % (17267)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.57  % (17280)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.57  % (17287)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.58  % (17273)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.58  % (17268)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.58  % (17270)Refutation found. Thanks to Tanya!
% 0.21/0.58  % SZS status Theorem for theBenchmark
% 0.21/0.58  % SZS output start Proof for theBenchmark
% 0.21/0.58  fof(f854,plain,(
% 0.21/0.58    $false),
% 0.21/0.58    inference(subsumption_resolution,[],[f853,f167])).
% 0.21/0.58  fof(f167,plain,(
% 0.21/0.58    m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.21/0.58    inference(subsumption_resolution,[],[f166,f46])).
% 0.21/0.58  fof(f46,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f4])).
% 0.21/0.58  fof(f4,axiom,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.58  fof(f166,plain,(
% 0.21/0.58    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | r1_tarski(sK1,sK1)),
% 0.21/0.58    inference(subsumption_resolution,[],[f165,f28])).
% 0.21/0.58  fof(f28,plain,(
% 0.21/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.58    inference(cnf_transformation,[],[f13])).
% 0.21/0.58  fof(f13,plain,(
% 0.21/0.58    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f12])).
% 0.21/0.58  fof(f12,plain,(
% 0.21/0.58    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> ~v1_subset_1(X1,u1_struct_0(X0))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f11])).
% 0.21/0.58  fof(f11,negated_conjecture,(
% 0.21/0.58    ~! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.21/0.58    inference(negated_conjecture,[],[f10])).
% 0.21/0.58  fof(f10,conjecture,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> ~v1_subset_1(X1,u1_struct_0(X0)))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_tex_2)).
% 0.21/0.58  fof(f165,plain,(
% 0.21/0.58    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,sK1)),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f163])).
% 0.21/0.58  fof(f163,plain,(
% 0.21/0.58    m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,sK1)),
% 0.21/0.58    inference(resolution,[],[f157,f50])).
% 0.21/0.58  fof(f50,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~r2_hidden(sK4(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r1_tarski(X1,X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f23])).
% 0.21/0.58  fof(f23,plain,(
% 0.21/0.58    ! [X0,X1] : (! [X2] : (r1_tarski(X1,X2) | ? [X3] : (~r2_hidden(X3,X2) & r2_hidden(X3,X1) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.58    inference(flattening,[],[f22])).
% 0.21/0.58  fof(f22,plain,(
% 0.21/0.58    ! [X0,X1] : (! [X2] : ((r1_tarski(X1,X2) | ? [X3] : ((~r2_hidden(X3,X2) & r2_hidden(X3,X1)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f2])).
% 0.21/0.58  fof(f2,axiom,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) => r2_hidden(X3,X2))) => r1_tarski(X1,X2))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_subset_1)).
% 0.21/0.58  fof(f157,plain,(
% 0.21/0.58    r2_hidden(sK4(u1_struct_0(sK0),sK1,sK1),sK1) | m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.21/0.58    inference(resolution,[],[f155,f46])).
% 0.21/0.58  fof(f155,plain,(
% 0.21/0.58    r1_tarski(sK1,sK1) | r2_hidden(sK4(u1_struct_0(sK0),sK1,sK1),sK1)),
% 0.21/0.58    inference(resolution,[],[f59,f28])).
% 0.21/0.58  fof(f59,plain,(
% 0.21/0.58    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK4(u1_struct_0(sK0),sK1,X1),sK1) | r1_tarski(sK1,X1)) )),
% 0.21/0.58    inference(resolution,[],[f28,f49])).
% 0.21/0.58  fof(f49,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r2_hidden(sK4(X0,X1,X2),X1) | r1_tarski(X1,X2)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f23])).
% 0.21/0.58  fof(f853,plain,(
% 0.21/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.21/0.58    inference(resolution,[],[f849,f53])).
% 0.21/0.58  fof(f53,plain,(
% 0.21/0.58    ( ! [X1] : (~v1_subset_1(X1,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X1))) )),
% 0.21/0.58    inference(equality_resolution,[],[f34])).
% 0.21/0.58  fof(f34,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 != X1 | ~v1_subset_1(X1,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f14])).
% 0.21/0.58  fof(f14,plain,(
% 0.21/0.58    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f7])).
% 0.21/0.58  fof(f7,axiom,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.58  fof(f849,plain,(
% 0.21/0.58    v1_subset_1(sK1,sK1)),
% 0.21/0.58    inference(resolution,[],[f772,f231])).
% 0.21/0.58  fof(f231,plain,(
% 0.21/0.58    ~v3_tex_2(sK1,sK0) | v1_subset_1(sK1,sK1)),
% 0.21/0.58    inference(backward_demodulation,[],[f27,f229])).
% 0.21/0.58  fof(f229,plain,(
% 0.21/0.58    sK1 = u1_struct_0(sK0)),
% 0.21/0.58    inference(subsumption_resolution,[],[f226,f28])).
% 0.21/0.58  fof(f226,plain,(
% 0.21/0.58    sK1 = u1_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f221])).
% 0.21/0.58  fof(f221,plain,(
% 0.21/0.58    sK1 = u1_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | sK1 = u1_struct_0(sK0)),
% 0.21/0.58    inference(resolution,[],[f112,f96])).
% 0.21/0.58  fof(f96,plain,(
% 0.21/0.58    v3_tex_2(sK1,sK0) | sK1 = u1_struct_0(sK0)),
% 0.21/0.58    inference(resolution,[],[f63,f26])).
% 0.21/0.58  fof(f26,plain,(
% 0.21/0.58    ~v1_subset_1(sK1,u1_struct_0(sK0)) | v3_tex_2(sK1,sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f13])).
% 0.21/0.58  fof(f63,plain,(
% 0.21/0.58    v1_subset_1(sK1,u1_struct_0(sK0)) | sK1 = u1_struct_0(sK0)),
% 0.21/0.58    inference(resolution,[],[f28,f33])).
% 0.21/0.58  fof(f33,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f14])).
% 0.21/0.58  fof(f112,plain,(
% 0.21/0.58    ( ! [X0] : (~v3_tex_2(X0,sK0) | u1_struct_0(sK0) = X0 | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f111,f47])).
% 0.21/0.58  fof(f47,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f4])).
% 0.21/0.58  fof(f111,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~r1_tarski(X0,u1_struct_0(sK0)) | u1_struct_0(sK0) = X0 | ~v3_tex_2(X0,sK0)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f110,f32])).
% 0.21/0.58  fof(f32,plain,(
% 0.21/0.58    l1_pre_topc(sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f13])).
% 0.21/0.58  fof(f110,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(X0,u1_struct_0(sK0)) | u1_struct_0(sK0) = X0 | ~v3_tex_2(X0,sK0)) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f101,f56])).
% 0.21/0.58  fof(f56,plain,(
% 0.21/0.58    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.58    inference(subsumption_resolution,[],[f55,f32])).
% 0.21/0.58  fof(f55,plain,(
% 0.21/0.58    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.58    inference(resolution,[],[f54,f42])).
% 0.21/0.58  fof(f42,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.58    inference(cnf_transformation,[],[f19])).
% 0.21/0.58  fof(f19,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f5])).
% 0.21/0.58  fof(f5,axiom,(
% 0.21/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.58  fof(f54,plain,(
% 0.21/0.58    m1_pre_topc(sK0,sK0)),
% 0.21/0.58    inference(resolution,[],[f32,f51])).
% 0.21/0.58  fof(f51,plain,(
% 0.21/0.58    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f24])).
% 0.21/0.58  fof(f24,plain,(
% 0.21/0.58    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f6])).
% 0.21/0.58  fof(f6,axiom,(
% 0.21/0.58    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.21/0.58  fof(f101,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~r1_tarski(X0,u1_struct_0(sK0)) | u1_struct_0(sK0) = X0 | ~v3_tex_2(X0,sK0)) )),
% 0.21/0.58    inference(resolution,[],[f94,f39])).
% 0.21/0.58  fof(f39,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~v2_tex_2(X2,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r1_tarski(X1,X2) | X1 = X2 | ~v3_tex_2(X1,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f16])).
% 0.21/0.58  fof(f16,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(flattening,[],[f15])).
% 0.21/0.58  fof(f15,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.58    inference(ennf_transformation,[],[f8])).
% 0.21/0.58  fof(f8,axiom,(
% 0.21/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 0.21/0.58  fof(f94,plain,(
% 0.21/0.58    v2_tex_2(u1_struct_0(sK0),sK0)),
% 0.21/0.58    inference(subsumption_resolution,[],[f93,f29])).
% 0.21/0.58  fof(f29,plain,(
% 0.21/0.58    ~v2_struct_0(sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f13])).
% 0.21/0.58  fof(f93,plain,(
% 0.21/0.58    v2_struct_0(sK0) | v2_tex_2(u1_struct_0(sK0),sK0)),
% 0.21/0.58    inference(subsumption_resolution,[],[f92,f32])).
% 0.21/0.58  fof(f92,plain,(
% 0.21/0.58    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_tex_2(u1_struct_0(sK0),sK0)),
% 0.21/0.58    inference(subsumption_resolution,[],[f91,f31])).
% 0.21/0.58  fof(f31,plain,(
% 0.21/0.58    v1_tdlat_3(sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f13])).
% 0.21/0.58  fof(f91,plain,(
% 0.21/0.58    ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_tex_2(u1_struct_0(sK0),sK0)),
% 0.21/0.58    inference(subsumption_resolution,[],[f84,f30])).
% 0.21/0.58  fof(f30,plain,(
% 0.21/0.58    v2_pre_topc(sK0)),
% 0.21/0.58    inference(cnf_transformation,[],[f13])).
% 0.21/0.58  fof(f84,plain,(
% 0.21/0.58    ~v2_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_tex_2(u1_struct_0(sK0),sK0)),
% 0.21/0.58    inference(resolution,[],[f56,f41])).
% 0.21/0.58  fof(f41,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v1_tdlat_3(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_tex_2(X1,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f18])).
% 0.21/0.58  fof(f18,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.58    inference(flattening,[],[f17])).
% 0.21/0.58  fof(f17,plain,(
% 0.21/0.58    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v1_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f9])).
% 0.21/0.58  fof(f9,axiom,(
% 0.21/0.58    ! [X0] : ((l1_pre_topc(X0) & v1_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => v2_tex_2(X1,X0)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_tex_2)).
% 0.21/0.58  fof(f27,plain,(
% 0.21/0.58    ~v3_tex_2(sK1,sK0) | v1_subset_1(sK1,u1_struct_0(sK0))),
% 0.21/0.58    inference(cnf_transformation,[],[f13])).
% 0.21/0.58  fof(f772,plain,(
% 0.21/0.58    v3_tex_2(sK1,sK0)),
% 0.21/0.58    inference(trivial_inequality_removal,[],[f645])).
% 0.21/0.58  fof(f645,plain,(
% 0.21/0.58    sK1 != sK1 | v3_tex_2(sK1,sK0)),
% 0.21/0.58    inference(backward_demodulation,[],[f80,f642])).
% 0.21/0.58  fof(f642,plain,(
% 0.21/0.58    sK1 = sK2(sK0,sK1)),
% 0.21/0.58    inference(subsumption_resolution,[],[f641,f557])).
% 0.21/0.58  fof(f557,plain,(
% 0.21/0.58    r2_hidden(sK3(sK1,sK1,sK2(sK0,sK1)),sK1) | sK1 = sK2(sK0,sK1)),
% 0.21/0.58    inference(resolution,[],[f177,f329])).
% 0.21/0.58  fof(f329,plain,(
% 0.21/0.58    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1))),
% 0.21/0.58    inference(subsumption_resolution,[],[f328,f167])).
% 0.21/0.58  fof(f328,plain,(
% 0.21/0.58    m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.21/0.58    inference(resolution,[],[f290,f53])).
% 0.21/0.58  fof(f290,plain,(
% 0.21/0.58    v1_subset_1(sK1,sK1) | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1))),
% 0.21/0.58    inference(forward_demodulation,[],[f256,f229])).
% 0.21/0.58  fof(f256,plain,(
% 0.21/0.58    v1_subset_1(sK1,sK1) | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.58    inference(backward_demodulation,[],[f134,f229])).
% 0.21/0.58  fof(f134,plain,(
% 0.21/0.58    v1_subset_1(sK1,u1_struct_0(sK0)) | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.58    inference(resolution,[],[f74,f27])).
% 0.21/0.58  fof(f74,plain,(
% 0.21/0.58    v3_tex_2(sK1,sK0) | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.58    inference(subsumption_resolution,[],[f73,f32])).
% 0.21/0.58  fof(f73,plain,(
% 0.21/0.58    ~l1_pre_topc(sK0) | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(sK1,sK0)),
% 0.21/0.58    inference(subsumption_resolution,[],[f68,f28])).
% 0.21/0.58  fof(f68,plain,(
% 0.21/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(sK1,sK0)),
% 0.21/0.58    inference(resolution,[],[f67,f35])).
% 0.21/0.58  fof(f35,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_tex_2(X1,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f16])).
% 0.21/0.58  fof(f67,plain,(
% 0.21/0.58    v2_tex_2(sK1,sK0)),
% 0.21/0.58    inference(subsumption_resolution,[],[f66,f29])).
% 0.21/0.58  fof(f66,plain,(
% 0.21/0.58    v2_struct_0(sK0) | v2_tex_2(sK1,sK0)),
% 0.21/0.58    inference(subsumption_resolution,[],[f65,f32])).
% 0.21/0.58  fof(f65,plain,(
% 0.21/0.58    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_tex_2(sK1,sK0)),
% 0.21/0.58    inference(subsumption_resolution,[],[f64,f31])).
% 0.21/0.58  fof(f64,plain,(
% 0.21/0.58    ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_tex_2(sK1,sK0)),
% 0.21/0.58    inference(subsumption_resolution,[],[f57,f30])).
% 0.21/0.58  fof(f57,plain,(
% 0.21/0.58    ~v2_pre_topc(sK0) | ~v1_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_tex_2(sK1,sK0)),
% 0.21/0.58    inference(resolution,[],[f28,f41])).
% 0.21/0.58  fof(f177,plain,(
% 0.21/0.58    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(sK1)) | r2_hidden(sK3(sK1,sK1,X2),sK1) | sK1 = X2) )),
% 0.21/0.58    inference(subsumption_resolution,[],[f174,f52])).
% 0.21/0.58  fof(f52,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~r2_hidden(X2,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | r2_hidden(X2,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f25])).
% 0.21/0.58  fof(f25,plain,(
% 0.21/0.58    ! [X0,X1] : (! [X2] : (r2_hidden(X2,X0) | ~r2_hidden(X2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f1])).
% 0.21/0.58  fof(f1,axiom,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (r2_hidden(X2,X1) => r2_hidden(X2,X0)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_subset_1)).
% 0.21/0.58  fof(f174,plain,(
% 0.21/0.58    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(sK1)) | r2_hidden(sK3(sK1,sK1,X2),X2) | r2_hidden(sK3(sK1,sK1,X2),sK1) | sK1 = X2) )),
% 0.21/0.58    inference(resolution,[],[f167,f43])).
% 0.21/0.58  fof(f43,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | r2_hidden(sK3(X0,X1,X2),X2) | r2_hidden(sK3(X0,X1,X2),X1) | X1 = X2) )),
% 0.21/0.58    inference(cnf_transformation,[],[f21])).
% 0.21/0.58  fof(f21,plain,(
% 0.21/0.58    ! [X0,X1] : (! [X2] : (X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.58    inference(flattening,[],[f20])).
% 0.21/0.58  fof(f20,plain,(
% 0.21/0.58    ! [X0,X1] : (! [X2] : ((X1 = X2 | ? [X3] : ((r2_hidden(X3,X1) <~> r2_hidden(X3,X2)) & m1_subset_1(X3,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.58    inference(ennf_transformation,[],[f3])).
% 0.21/0.58  fof(f3,axiom,(
% 0.21/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => (! [X3] : (m1_subset_1(X3,X0) => (r2_hidden(X3,X1) <=> r2_hidden(X3,X2))) => X1 = X2)))),
% 0.21/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_subset_1)).
% 0.21/0.58  fof(f641,plain,(
% 0.21/0.58    sK1 = sK2(sK0,sK1) | ~r2_hidden(sK3(sK1,sK1,sK2(sK0,sK1)),sK1)),
% 0.21/0.58    inference(subsumption_resolution,[],[f640,f167])).
% 0.21/0.58  fof(f640,plain,(
% 0.21/0.58    sK1 = sK2(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~r2_hidden(sK3(sK1,sK1,sK2(sK0,sK1)),sK1)),
% 0.21/0.58    inference(subsumption_resolution,[],[f639,f329])).
% 0.21/0.58  fof(f639,plain,(
% 0.21/0.58    sK1 = sK2(sK0,sK1) | ~m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~r2_hidden(sK3(sK1,sK1,sK2(sK0,sK1)),sK1)),
% 0.21/0.58    inference(duplicate_literal_removal,[],[f637])).
% 0.21/0.58  fof(f637,plain,(
% 0.21/0.58    sK1 = sK2(sK0,sK1) | ~m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK1)) | ~r2_hidden(sK3(sK1,sK1,sK2(sK0,sK1)),sK1) | sK1 = sK2(sK0,sK1)),
% 0.21/0.58    inference(resolution,[],[f635,f44])).
% 0.21/0.58  fof(f44,plain,(
% 0.21/0.58    ( ! [X2,X0,X1] : (~r2_hidden(sK3(X0,X1,X2),X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~r2_hidden(sK3(X0,X1,X2),X1) | X1 = X2) )),
% 0.21/0.58    inference(cnf_transformation,[],[f21])).
% 0.21/0.58  fof(f635,plain,(
% 0.21/0.58    r2_hidden(sK3(sK1,sK1,sK2(sK0,sK1)),sK2(sK0,sK1)) | sK1 = sK2(sK0,sK1)),
% 0.21/0.58    inference(resolution,[],[f589,f326])).
% 0.21/0.58  fof(f326,plain,(
% 0.21/0.58    m1_subset_1(sK1,k1_zfmisc_1(sK2(sK0,sK1)))),
% 0.21/0.58    inference(resolution,[],[f322,f46])).
% 0.21/0.58  fof(f322,plain,(
% 0.21/0.58    r1_tarski(sK1,sK2(sK0,sK1))),
% 0.21/0.58    inference(subsumption_resolution,[],[f321,f167])).
% 0.21/0.58  fof(f321,plain,(
% 0.21/0.58    r1_tarski(sK1,sK2(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK1))),
% 0.21/0.58    inference(resolution,[],[f255,f53])).
% 0.21/0.58  fof(f255,plain,(
% 0.21/0.58    v1_subset_1(sK1,sK1) | r1_tarski(sK1,sK2(sK0,sK1))),
% 0.21/0.58    inference(backward_demodulation,[],[f131,f229])).
% 0.21/0.58  fof(f131,plain,(
% 0.21/0.58    v1_subset_1(sK1,u1_struct_0(sK0)) | r1_tarski(sK1,sK2(sK0,sK1))),
% 0.21/0.58    inference(resolution,[],[f78,f27])).
% 0.21/0.58  fof(f78,plain,(
% 0.21/0.58    v3_tex_2(sK1,sK0) | r1_tarski(sK1,sK2(sK0,sK1))),
% 0.21/0.58    inference(subsumption_resolution,[],[f77,f32])).
% 0.21/0.58  fof(f77,plain,(
% 0.21/0.58    ~l1_pre_topc(sK0) | r1_tarski(sK1,sK2(sK0,sK1)) | v3_tex_2(sK1,sK0)),
% 0.21/0.58    inference(subsumption_resolution,[],[f70,f28])).
% 0.21/0.58  fof(f70,plain,(
% 0.21/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | r1_tarski(sK1,sK2(sK0,sK1)) | v3_tex_2(sK1,sK0)),
% 0.21/0.58    inference(resolution,[],[f67,f37])).
% 0.21/0.58  fof(f37,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(X1,sK2(X0,X1)) | v3_tex_2(X1,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f16])).
% 0.21/0.58  fof(f589,plain,(
% 0.21/0.58    ( ! [X0] : (~m1_subset_1(sK1,k1_zfmisc_1(X0)) | sK1 = sK2(sK0,sK1) | r2_hidden(sK3(sK1,sK1,sK2(sK0,sK1)),X0)) )),
% 0.21/0.58    inference(resolution,[],[f557,f52])).
% 0.21/0.58  fof(f80,plain,(
% 0.21/0.58    sK1 != sK2(sK0,sK1) | v3_tex_2(sK1,sK0)),
% 0.21/0.58    inference(subsumption_resolution,[],[f79,f32])).
% 0.21/0.58  fof(f79,plain,(
% 0.21/0.58    ~l1_pre_topc(sK0) | sK1 != sK2(sK0,sK1) | v3_tex_2(sK1,sK0)),
% 0.21/0.58    inference(subsumption_resolution,[],[f71,f28])).
% 0.21/0.58  fof(f71,plain,(
% 0.21/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | sK1 != sK2(sK0,sK1) | v3_tex_2(sK1,sK0)),
% 0.21/0.58    inference(resolution,[],[f67,f38])).
% 0.21/0.58  fof(f38,plain,(
% 0.21/0.58    ( ! [X0,X1] : (~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | sK2(X0,X1) != X1 | v3_tex_2(X1,X0)) )),
% 0.21/0.58    inference(cnf_transformation,[],[f16])).
% 0.21/0.58  % SZS output end Proof for theBenchmark
% 0.21/0.58  % (17270)------------------------------
% 0.21/0.58  % (17270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.58  % (17270)Termination reason: Refutation
% 0.21/0.58  
% 0.21/0.58  % (17270)Memory used [KB]: 6396
% 0.21/0.58  % (17270)Time elapsed: 0.160 s
% 0.21/0.58  % (17270)------------------------------
% 0.21/0.58  % (17270)------------------------------
% 0.21/0.58  % (17264)Success in time 0.224 s
%------------------------------------------------------------------------------
