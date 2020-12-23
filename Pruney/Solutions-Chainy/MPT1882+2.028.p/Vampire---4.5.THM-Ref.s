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
% DateTime   : Thu Dec  3 13:22:03 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 904 expanded)
%              Number of leaves         :   10 ( 161 expanded)
%              Depth                    :   21
%              Number of atoms          :  349 (5400 expanded)
%              Number of equality atoms :   24 (  66 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f300,plain,(
    $false ),
    inference(subsumption_resolution,[],[f295,f41])).

fof(f41,plain,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    inference(cnf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] : r1_tarski(k1_xboole_0,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

fof(f295,plain,(
    ~ r1_tarski(k1_xboole_0,sK1) ),
    inference(backward_demodulation,[],[f267,f291])).

fof(f291,plain,(
    k1_xboole_0 = sK2(sK0,sK1) ),
    inference(resolution,[],[f289,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(resolution,[],[f60,f39])).

fof(f39,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
      | X0 = X1
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ~ ( v1_xboole_0(X1)
        & X0 != X1
        & v1_xboole_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).

fof(f289,plain,(
    v1_xboole_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f288,f268])).

fof(f268,plain,(
    sK1 != sK2(sK0,sK1) ),
    inference(subsumption_resolution,[],[f172,f264])).

fof(f264,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f261,f174])).

fof(f174,plain,(
    v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f31,f170])).

fof(f170,plain,(
    ~ v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f169,f32])).

fof(f32,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | ~ v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_tex_2(X1,X0)
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
          ( ( v3_tex_2(X1,X0)
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
           => ( v3_tex_2(X1,X0)
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
         => ( v3_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).

fof(f169,plain,
    ( v1_zfmisc_1(sK1)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f167,f100])).

fof(f100,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f97,f34])).

fof(f34,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f97,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(X0,sK0)
      | ~ v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f50,f38])).

fof(f38,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).

fof(f167,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f164,f34])).

fof(f164,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_zfmisc_1(X0)
      | ~ v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f163,f38])).

fof(f163,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_zfmisc_1(X0)
      | ~ v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f162,f35])).

fof(f35,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f162,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_zfmisc_1(X0)
      | ~ v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f161,f36])).

fof(f36,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f161,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_zfmisc_1(X0)
      | ~ v2_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f64,f37])).

fof(f37,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(subsumption_resolution,[],[f53,f51])).

fof(f51,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f53,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_tex_2(X1,X0)
          <=> v1_zfmisc_1(X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f31,plain,
    ( v3_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f261,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f258,f34])).

fof(f258,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_zfmisc_1(X0)
      | v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f257,f116])).

fof(f116,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_xboole_0(X0)
      | v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f115,f38])).

fof(f115,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f114,f35])).

fof(f114,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f54,f36])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v2_tex_2(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
          | ~ v1_xboole_0(X1) )
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
            & v1_xboole_0(X1) )
         => v2_tex_2(X1,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).

fof(f257,plain,(
    ! [X0] :
      ( v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_zfmisc_1(X0)
      | v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f256,f38])).

fof(f256,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_zfmisc_1(X0)
      | v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f255,f35])).

fof(f255,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_zfmisc_1(X0)
      | v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f254,f36])).

fof(f254,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v1_zfmisc_1(X0)
      | v2_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f52,f37])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v1_zfmisc_1(X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f172,plain,
    ( sK1 != sK2(sK0,sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f152,f170])).

fof(f152,plain,
    ( sK1 != sK2(sK0,sK1)
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f149,f34])).

fof(f149,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | sK2(sK0,X0) != X0
      | v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f48,f38])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | sK2(X0,X1) != X1
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f288,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | sK1 = sK2(sK0,sK1) ),
    inference(subsumption_resolution,[],[f283,f33])).

fof(f33,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f283,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK2(sK0,sK1))
    | sK1 = sK2(sK0,sK1) ),
    inference(resolution,[],[f265,f269])).

fof(f269,plain,(
    r1_tarski(sK1,sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f173,f264])).

fof(f173,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f141,f170])).

fof(f141,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f138,f34])).

fof(f138,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | r1_tarski(X0,sK2(sK0,X0))
      | v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f47,f38])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | r1_tarski(X1,sK2(X0,X1))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f265,plain,(
    ! [X0] :
      ( ~ r1_tarski(X0,sK2(sK0,sK1))
      | v1_xboole_0(X0)
      | v1_xboole_0(sK2(sK0,sK1))
      | sK2(sK0,sK1) = X0 ) ),
    inference(subsumption_resolution,[],[f225,f264])).

fof(f225,plain,(
    ! [X0] :
      ( ~ v2_tex_2(sK1,sK0)
      | v1_xboole_0(sK2(sK0,sK1))
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,sK2(sK0,sK1))
      | sK2(sK0,sK1) = X0 ) ),
    inference(resolution,[],[f222,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).

fof(f222,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f219,f170])).

fof(f219,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | v3_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK2(sK0,sK1)) ),
    inference(resolution,[],[f189,f34])).

fof(f189,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v3_tex_2(X0,sK0)
      | v1_zfmisc_1(sK2(sK0,X0)) ) ),
    inference(subsumption_resolution,[],[f188,f137])).

fof(f137,plain,(
    ! [X0] :
      ( v2_tex_2(sK2(sK0,X0),sK0)
      | ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f46,f38])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | v2_tex_2(sK2(X0,X1),X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f188,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v3_tex_2(X0,sK0)
      | v1_zfmisc_1(sK2(sK0,X0))
      | ~ v2_tex_2(sK2(sK0,X0),sK0) ) ),
    inference(subsumption_resolution,[],[f182,f38])).

fof(f182,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | v3_tex_2(X0,sK0)
      | v1_zfmisc_1(sK2(sK0,X0))
      | ~ v2_tex_2(sK2(sK0,X0),sK0) ) ),
    inference(resolution,[],[f45,f164])).

fof(f45,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f267,plain,(
    ~ r1_tarski(sK2(sK0,sK1),sK1) ),
    inference(subsumption_resolution,[],[f171,f264])).

fof(f171,plain,
    ( ~ r1_tarski(sK2(sK0,sK1),sK1)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f154,f170])).

fof(f154,plain,
    ( ~ r1_tarski(sK2(sK0,sK1),sK1)
    | v3_tex_2(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f143,f152])).

fof(f143,plain,
    ( ~ r1_tarski(sK2(sK0,sK1),sK1)
    | v3_tex_2(sK1,sK0)
    | ~ v2_tex_2(sK1,sK0)
    | sK1 = sK2(sK0,sK1) ),
    inference(resolution,[],[f141,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 18:34:00 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.47  % (22889)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.20/0.48  % (22905)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.20/0.49  % (22891)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.20/0.49  % (22905)Refutation found. Thanks to Tanya!
% 0.20/0.49  % SZS status Theorem for theBenchmark
% 0.20/0.49  % SZS output start Proof for theBenchmark
% 0.20/0.49  fof(f300,plain,(
% 0.20/0.49    $false),
% 0.20/0.49    inference(subsumption_resolution,[],[f295,f41])).
% 0.20/0.49  fof(f41,plain,(
% 0.20/0.49    ( ! [X0] : (r1_tarski(k1_xboole_0,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f5])).
% 0.20/0.49  fof(f5,axiom,(
% 0.20/0.49    ! [X0] : r1_tarski(k1_xboole_0,X0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).
% 0.20/0.49  fof(f295,plain,(
% 0.20/0.49    ~r1_tarski(k1_xboole_0,sK1)),
% 0.20/0.49    inference(backward_demodulation,[],[f267,f291])).
% 0.20/0.49  fof(f291,plain,(
% 0.20/0.49    k1_xboole_0 = sK2(sK0,sK1)),
% 0.20/0.49    inference(resolution,[],[f289,f70])).
% 0.20/0.49  fof(f70,plain,(
% 0.20/0.49    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.20/0.49    inference(resolution,[],[f60,f39])).
% 0.20/0.49  fof(f39,plain,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    inference(cnf_transformation,[],[f1])).
% 0.20/0.49  fof(f1,axiom,(
% 0.20/0.49    v1_xboole_0(k1_xboole_0)),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.49  fof(f60,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f29])).
% 0.20/0.49  fof(f29,plain,(
% 0.20/0.49    ! [X0,X1] : (~v1_xboole_0(X1) | X0 = X1 | ~v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f6])).
% 0.20/0.49  fof(f6,axiom,(
% 0.20/0.49    ! [X0,X1] : ~(v1_xboole_0(X1) & X0 != X1 & v1_xboole_0(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_boole)).
% 0.20/0.49  fof(f289,plain,(
% 0.20/0.49    v1_xboole_0(sK2(sK0,sK1))),
% 0.20/0.49    inference(subsumption_resolution,[],[f288,f268])).
% 0.20/0.49  fof(f268,plain,(
% 0.20/0.49    sK1 != sK2(sK0,sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f172,f264])).
% 0.20/0.49  fof(f264,plain,(
% 0.20/0.49    v2_tex_2(sK1,sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f261,f174])).
% 0.20/0.49  fof(f174,plain,(
% 0.20/0.49    v1_zfmisc_1(sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f31,f170])).
% 0.20/0.49  fof(f170,plain,(
% 0.20/0.49    ~v3_tex_2(sK1,sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f169,f32])).
% 0.20/0.49  fof(f32,plain,(
% 0.20/0.49    ~v3_tex_2(sK1,sK0) | ~v1_zfmisc_1(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f18,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f17])).
% 0.20/0.49  fof(f17,plain,(
% 0.20/0.49    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f16])).
% 0.20/0.49  fof(f16,negated_conjecture,(
% 0.20/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.20/0.49    inference(negated_conjecture,[],[f15])).
% 0.20/0.49  fof(f15,conjecture,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_tex_2)).
% 0.20/0.49  fof(f169,plain,(
% 0.20/0.49    v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)),
% 0.20/0.49    inference(resolution,[],[f167,f100])).
% 0.20/0.49  fof(f100,plain,(
% 0.20/0.49    v2_tex_2(sK1,sK0) | ~v3_tex_2(sK1,sK0)),
% 0.20/0.49    inference(resolution,[],[f97,f34])).
% 0.20/0.49  fof(f34,plain,(
% 0.20/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f97,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0) | ~v3_tex_2(X0,sK0)) )),
% 0.20/0.49    inference(resolution,[],[f50,f38])).
% 0.20/0.49  fof(f38,plain,(
% 0.20/0.49    l1_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f50,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0) | ~v3_tex_2(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f23,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(flattening,[],[f22])).
% 0.20/0.49  fof(f22,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f11])).
% 0.20/0.49  fof(f11,axiom,(
% 0.20/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_tex_2)).
% 0.20/0.49  fof(f167,plain,(
% 0.20/0.49    ~v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1)),
% 0.20/0.49    inference(resolution,[],[f164,f34])).
% 0.20/0.49  fof(f164,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(X0) | ~v2_tex_2(X0,sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f163,f38])).
% 0.20/0.49  fof(f163,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(X0) | ~v2_tex_2(X0,sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f162,f35])).
% 0.20/0.49  fof(f35,plain,(
% 0.20/0.49    ~v2_struct_0(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f162,plain,(
% 0.20/0.49    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(X0) | ~v2_tex_2(X0,sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f161,f36])).
% 0.20/0.49  fof(f36,plain,(
% 0.20/0.49    v2_pre_topc(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f161,plain,(
% 0.20/0.49    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(X0) | ~v2_tex_2(X0,sK0)) )),
% 0.20/0.49    inference(resolution,[],[f64,f37])).
% 0.20/0.49  fof(f37,plain,(
% 0.20/0.49    v2_tdlat_3(sK0)),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f64,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f53,f51])).
% 0.20/0.49  fof(f51,plain,(
% 0.20/0.49    ( ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f24])).
% 0.20/0.49  fof(f24,plain,(
% 0.20/0.49    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f7])).
% 0.20/0.49  fof(f7,axiom,(
% 0.20/0.49    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 0.20/0.49  fof(f53,plain,(
% 0.20/0.49    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f26,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f25])).
% 0.20/0.49  fof(f25,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f14])).
% 0.20/0.49  fof(f14,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_tex_2)).
% 0.20/0.49  fof(f31,plain,(
% 0.20/0.49    v3_tex_2(sK1,sK0) | v1_zfmisc_1(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f261,plain,(
% 0.20/0.49    ~v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 0.20/0.49    inference(resolution,[],[f258,f34])).
% 0.20/0.49  fof(f258,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_zfmisc_1(X0) | v2_tex_2(X0,sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f257,f116])).
% 0.20/0.49  fof(f116,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_xboole_0(X0) | v2_tex_2(X0,sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f115,f38])).
% 0.20/0.49  fof(f115,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_pre_topc(sK0) | ~v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f114,f35])).
% 0.20/0.49  fof(f114,plain,(
% 0.20/0.49    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(X0,sK0)) )),
% 0.20/0.49    inference(resolution,[],[f54,f36])).
% 0.20/0.49  fof(f54,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | ~v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f28])).
% 0.20/0.49  fof(f28,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.49    inference(flattening,[],[f27])).
% 0.20/0.49  fof(f27,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (v2_tex_2(X1,X0) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.49    inference(ennf_transformation,[],[f13])).
% 0.20/0.49  fof(f13,axiom,(
% 0.20/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & v1_xboole_0(X1)) => v2_tex_2(X1,X0)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_tex_2)).
% 0.20/0.49  fof(f257,plain,(
% 0.20/0.49    ( ! [X0] : (v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_zfmisc_1(X0) | v2_tex_2(X0,sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f256,f38])).
% 0.20/0.49  fof(f256,plain,(
% 0.20/0.49    ( ! [X0] : (~l1_pre_topc(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_zfmisc_1(X0) | v2_tex_2(X0,sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f255,f35])).
% 0.20/0.49  fof(f255,plain,(
% 0.20/0.49    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_zfmisc_1(X0) | v2_tex_2(X0,sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f254,f36])).
% 0.20/0.49  fof(f254,plain,(
% 0.20/0.49    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v1_zfmisc_1(X0) | v2_tex_2(X0,sK0)) )),
% 0.20/0.49    inference(resolution,[],[f52,f37])).
% 0.20/0.49  fof(f52,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f26])).
% 0.20/0.49  fof(f172,plain,(
% 0.20/0.49    sK1 != sK2(sK0,sK1) | ~v2_tex_2(sK1,sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f152,f170])).
% 0.20/0.49  fof(f152,plain,(
% 0.20/0.49    sK1 != sK2(sK0,sK1) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0)),
% 0.20/0.49    inference(resolution,[],[f149,f34])).
% 0.20/0.49  fof(f149,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | sK2(sK0,X0) != X0 | v3_tex_2(X0,sK0)) )),
% 0.20/0.49    inference(resolution,[],[f48,f38])).
% 0.20/0.49  fof(f48,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | sK2(X0,X1) != X1 | v3_tex_2(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f288,plain,(
% 0.20/0.49    v1_xboole_0(sK2(sK0,sK1)) | sK1 = sK2(sK0,sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f283,f33])).
% 0.20/0.49  fof(f33,plain,(
% 0.20/0.49    ~v1_xboole_0(sK1)),
% 0.20/0.49    inference(cnf_transformation,[],[f18])).
% 0.20/0.49  fof(f283,plain,(
% 0.20/0.49    v1_xboole_0(sK1) | v1_xboole_0(sK2(sK0,sK1)) | sK1 = sK2(sK0,sK1)),
% 0.20/0.49    inference(resolution,[],[f265,f269])).
% 0.20/0.49  fof(f269,plain,(
% 0.20/0.49    r1_tarski(sK1,sK2(sK0,sK1))),
% 0.20/0.49    inference(subsumption_resolution,[],[f173,f264])).
% 0.20/0.49  fof(f173,plain,(
% 0.20/0.49    r1_tarski(sK1,sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f141,f170])).
% 0.20/0.49  fof(f141,plain,(
% 0.20/0.49    r1_tarski(sK1,sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0)),
% 0.20/0.49    inference(resolution,[],[f138,f34])).
% 0.20/0.49  fof(f138,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | r1_tarski(X0,sK2(sK0,X0)) | v3_tex_2(X0,sK0)) )),
% 0.20/0.49    inference(resolution,[],[f47,f38])).
% 0.20/0.49  fof(f47,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | r1_tarski(X1,sK2(X0,X1)) | v3_tex_2(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f265,plain,(
% 0.20/0.49    ( ! [X0] : (~r1_tarski(X0,sK2(sK0,sK1)) | v1_xboole_0(X0) | v1_xboole_0(sK2(sK0,sK1)) | sK2(sK0,sK1) = X0) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f225,f264])).
% 0.20/0.49  fof(f225,plain,(
% 0.20/0.49    ( ! [X0] : (~v2_tex_2(sK1,sK0) | v1_xboole_0(sK2(sK0,sK1)) | v1_xboole_0(X0) | ~r1_tarski(X0,sK2(sK0,sK1)) | sK2(sK0,sK1) = X0) )),
% 0.20/0.49    inference(resolution,[],[f222,f44])).
% 0.20/0.49  fof(f44,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f21])).
% 0.20/0.49  fof(f21,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.49    inference(flattening,[],[f20])).
% 0.20/0.49  fof(f20,plain,(
% 0.20/0.49    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.20/0.49    inference(ennf_transformation,[],[f12])).
% 0.20/0.49  fof(f12,axiom,(
% 0.20/0.49    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tex_2)).
% 0.20/0.49  fof(f222,plain,(
% 0.20/0.49    v1_zfmisc_1(sK2(sK0,sK1)) | ~v2_tex_2(sK1,sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f219,f170])).
% 0.20/0.49  fof(f219,plain,(
% 0.20/0.49    ~v2_tex_2(sK1,sK0) | v3_tex_2(sK1,sK0) | v1_zfmisc_1(sK2(sK0,sK1))),
% 0.20/0.49    inference(resolution,[],[f189,f34])).
% 0.20/0.49  fof(f189,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v3_tex_2(X0,sK0) | v1_zfmisc_1(sK2(sK0,X0))) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f188,f137])).
% 0.20/0.49  fof(f137,plain,(
% 0.20/0.49    ( ! [X0] : (v2_tex_2(sK2(sK0,X0),sK0) | ~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(X0,sK0)) )),
% 0.20/0.49    inference(resolution,[],[f46,f38])).
% 0.20/0.49  fof(f46,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | v2_tex_2(sK2(X0,X1),X0) | v3_tex_2(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f188,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v3_tex_2(X0,sK0) | v1_zfmisc_1(sK2(sK0,X0)) | ~v2_tex_2(sK2(sK0,X0),sK0)) )),
% 0.20/0.49    inference(subsumption_resolution,[],[f182,f38])).
% 0.20/0.49  fof(f182,plain,(
% 0.20/0.49    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~l1_pre_topc(sK0) | v3_tex_2(X0,sK0) | v1_zfmisc_1(sK2(sK0,X0)) | ~v2_tex_2(sK2(sK0,X0),sK0)) )),
% 0.20/0.49    inference(resolution,[],[f45,f164])).
% 0.20/0.49  fof(f45,plain,(
% 0.20/0.49    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~l1_pre_topc(X0) | v3_tex_2(X1,X0)) )),
% 0.20/0.49    inference(cnf_transformation,[],[f23])).
% 0.20/0.49  fof(f267,plain,(
% 0.20/0.49    ~r1_tarski(sK2(sK0,sK1),sK1)),
% 0.20/0.49    inference(subsumption_resolution,[],[f171,f264])).
% 0.20/0.49  fof(f171,plain,(
% 0.20/0.49    ~r1_tarski(sK2(sK0,sK1),sK1) | ~v2_tex_2(sK1,sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f154,f170])).
% 0.20/0.49  fof(f154,plain,(
% 0.20/0.49    ~r1_tarski(sK2(sK0,sK1),sK1) | v3_tex_2(sK1,sK0) | ~v2_tex_2(sK1,sK0)),
% 0.20/0.49    inference(subsumption_resolution,[],[f143,f152])).
% 0.20/0.49  fof(f143,plain,(
% 0.20/0.49    ~r1_tarski(sK2(sK0,sK1),sK1) | v3_tex_2(sK1,sK0) | ~v2_tex_2(sK1,sK0) | sK1 = sK2(sK0,sK1)),
% 0.20/0.49    inference(resolution,[],[f141,f57])).
% 0.20/0.49  fof(f57,plain,(
% 0.20/0.49    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.49    inference(cnf_transformation,[],[f2])).
% 0.20/0.49  fof(f2,axiom,(
% 0.20/0.49    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.49    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.49  % SZS output end Proof for theBenchmark
% 0.20/0.49  % (22905)------------------------------
% 0.20/0.49  % (22905)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.49  % (22905)Termination reason: Refutation
% 0.20/0.49  
% 0.20/0.49  % (22905)Memory used [KB]: 1791
% 0.20/0.49  % (22905)Time elapsed: 0.077 s
% 0.20/0.49  % (22905)------------------------------
% 0.20/0.49  % (22905)------------------------------
% 0.20/0.49  % (22881)Success in time 0.131 s
%------------------------------------------------------------------------------
