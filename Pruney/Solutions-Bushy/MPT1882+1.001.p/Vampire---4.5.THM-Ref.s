%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1882+1.001 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n026.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 08:50:50 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 0.22s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 787 expanded)
%              Number of leaves         :    6 ( 137 expanded)
%              Depth                    :   26
%              Number of atoms          :  321 (4876 expanded)
%              Number of equality atoms :   14 (  50 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f117,plain,(
    $false ),
    inference(subsumption_resolution,[],[f116,f19])).

fof(f19,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,plain,(
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
    inference(flattening,[],[f8])).

fof(f8,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,negated_conjecture,(
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
    inference(negated_conjecture,[],[f6])).

fof(f6,conjecture,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).

fof(f116,plain,(
    v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f114,f113])).

fof(f113,plain,(
    v1_xboole_0(sK2(sK0,sK1)) ),
    inference(global_subsumption,[],[f18,f69,f112])).

fof(f112,plain,
    ( v3_tex_2(sK1,sK0)
    | v1_xboole_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f111,f63])).

fof(f63,plain,
    ( sK1 != sK2(sK0,sK1)
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f62,f24])).

fof(f24,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f62,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 != sK2(sK0,sK1)
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f54,f20])).

fof(f20,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f9])).

fof(f54,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | sK1 != sK2(sK0,sK1)
    | v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f49,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | sK2(X0,X1) != X1
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
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

fof(f49,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f48,f39])).

fof(f39,plain,
    ( v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f38,f24])).

fof(f38,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f37,f20])).

fof(f37,plain,
    ( v1_zfmisc_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f17,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f17,plain,
    ( v3_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f48,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f47,f21])).

fof(f21,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f47,plain,
    ( v2_struct_0(sK0)
    | ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f46,f19])).

fof(f46,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f45,f24])).

fof(f45,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f44,f23])).

fof(f23,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f44,plain,
    ( ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f41,f22])).

fof(f22,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f9])).

fof(f41,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f20,f25])).

fof(f25,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v1_zfmisc_1(X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,plain,(
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
    inference(flattening,[],[f10])).

fof(f10,plain,(
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f111,plain,
    ( v3_tex_2(sK1,sK0)
    | v1_xboole_0(sK2(sK0,sK1))
    | sK1 = sK2(sK0,sK1) ),
    inference(subsumption_resolution,[],[f110,f103])).

fof(f103,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK2(sK0,sK1)) ),
    inference(global_subsumption,[],[f18,f69,f102])).

fof(f102,plain,
    ( v3_tex_2(sK1,sK0)
    | v1_xboole_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f101,f57])).

fof(f57,plain,
    ( m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f56,f24])).

fof(f56,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f51,f20])).

fof(f51,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f49,f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f101,plain,
    ( v3_tex_2(sK1,sK0)
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f100,f21])).

fof(f100,plain,
    ( v3_tex_2(sK1,sK0)
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f99,f24])).

fof(f99,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f98,f23])).

fof(f98,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f85,f22])).

fof(f85,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f59,f26])).

fof(f26,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_zfmisc_1(X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f11])).

fof(f59,plain,
    ( v2_tex_2(sK2(sK0,sK1),sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f58,f24])).

fof(f58,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tex_2(sK2(sK0,sK1),sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f52,f20])).

fof(f52,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v2_tex_2(sK2(sK0,sK1),sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f49,f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_tex_2(sK2(X0,X1),X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f110,plain,
    ( v3_tex_2(sK1,sK0)
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ v1_zfmisc_1(sK2(sK0,sK1))
    | sK1 = sK2(sK0,sK1) ),
    inference(subsumption_resolution,[],[f106,f19])).

fof(f106,plain,
    ( v3_tex_2(sK1,sK0)
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ v1_zfmisc_1(sK2(sK0,sK1))
    | v1_xboole_0(sK1)
    | sK1 = sK2(sK0,sK1) ),
    inference(resolution,[],[f61,f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | v1_xboole_0(X1)
      | ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f61,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f60,f24])).

fof(f60,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(sK1,sK2(sK0,sK1))
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f53,f20])).

fof(f53,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | r1_tarski(sK1,sK2(sK0,sK1))
    | v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f49,f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(X1,sK2(X0,X1))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f69,plain,(
    v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f68,f21])).

fof(f68,plain,
    ( v1_zfmisc_1(sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f67,f20])).

fof(f67,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f66,f19])).

fof(f66,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f65,f24])).

fof(f65,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f64,f23])).

fof(f64,plain,
    ( ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f55,f22])).

fof(f55,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK1)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f49,f26])).

fof(f18,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | ~ v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f9])).

fof(f114,plain,
    ( ~ v1_xboole_0(sK2(sK0,sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f107,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f107,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK2(sK0,sK1))) ),
    inference(global_subsumption,[],[f18,f69,f104])).

fof(f104,plain,
    ( v3_tex_2(sK1,sK0)
    | m1_subset_1(sK1,k1_zfmisc_1(sK2(sK0,sK1))) ),
    inference(resolution,[],[f61,f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

%------------------------------------------------------------------------------
