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
% DateTime   : Thu Dec  3 13:21:59 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :   89 (1104 expanded)
%              Number of leaves         :    8 ( 193 expanded)
%              Depth                    :   27
%              Number of atoms          :  336 (6780 expanded)
%              Number of equality atoms :   11 (  59 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f151,plain,(
    $false ),
    inference(subsumption_resolution,[],[f150,f29])).

fof(f29,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,plain,(
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
    inference(flattening,[],[f12])).

fof(f12,plain,(
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
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
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
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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

fof(f150,plain,(
    v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f149,f140])).

fof(f140,plain,(
    ~ v1_xboole_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f138,f29])).

fof(f138,plain,
    ( ~ v1_xboole_0(sK2(sK0,sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f135,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_xboole_0(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).

fof(f135,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(sK2(sK0,sK1))) ),
    inference(resolution,[],[f134,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f134,plain,(
    r1_tarski(sK1,sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f132,f91])).

fof(f91,plain,(
    v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f90,f31])).

fof(f31,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f90,plain,
    ( v1_zfmisc_1(sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f89,f30])).

fof(f30,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f89,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f88,f29])).

fof(f88,plain,
    ( v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f87,f34])).

fof(f34,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f87,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f86,f33])).

fof(f33,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f86,plain,
    ( ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK1)
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f75,f32])).

fof(f32,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f13])).

fof(f75,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK1)
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f68,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_zfmisc_1(X1)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
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

fof(f68,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f67,f56])).

fof(f56,plain,
    ( v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f55,f34])).

fof(f55,plain,
    ( v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f54,f30])).

fof(f54,plain,
    ( v1_zfmisc_1(sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f27,f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ~ v3_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f27,plain,
    ( v3_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f67,plain,
    ( ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f66,f31])).

fof(f66,plain,
    ( v2_struct_0(sK0)
    | ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f65,f29])).

fof(f65,plain,
    ( v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f64,f34])).

fof(f64,plain,
    ( ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f63,f33])).

fof(f63,plain,
    ( ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f59,f32])).

fof(f59,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK1)
    | v2_struct_0(sK0)
    | ~ v1_zfmisc_1(sK1)
    | v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f30,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | v2_struct_0(X0)
      | ~ v1_zfmisc_1(X1)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f132,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | ~ v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f81,f28])).

fof(f28,plain,
    ( ~ v3_tex_2(sK1,sK0)
    | ~ v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f13])).

fof(f81,plain,
    ( v3_tex_2(sK1,sK0)
    | r1_tarski(sK1,sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f80,f34])).

fof(f80,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(sK1,sK2(sK0,sK1))
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f72,f30])).

fof(f72,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | r1_tarski(sK1,sK2(sK0,sK1))
    | v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f68,f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r1_tarski(X1,sK2(X0,X1))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f149,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f148,f135])).

fof(f148,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(sK2(sK0,sK1)))
    | v1_xboole_0(sK2(sK0,sK1))
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f147,f131])).

fof(f131,plain,(
    v1_zfmisc_1(sK2(sK0,sK1)) ),
    inference(global_subsumption,[],[f28,f91,f130])).

fof(f130,plain,
    ( v3_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f129,f77])).

fof(f77,plain,
    ( v3_tex_2(sK1,sK0)
    | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f76,f34])).

fof(f76,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f70,f30])).

fof(f70,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f68,f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f129,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f128,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | v1_zfmisc_1(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( v1_zfmisc_1(X0)
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => v1_zfmisc_1(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).

fof(f128,plain,
    ( v3_tex_2(sK1,sK0)
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f127,f31])).

fof(f127,plain,
    ( v3_tex_2(sK1,sK0)
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f126,f34])).

fof(f126,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f125,f33])).

fof(f125,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f109,f32])).

fof(f109,plain,
    ( v3_tex_2(sK1,sK0)
    | ~ v2_pre_topc(sK0)
    | ~ v2_tdlat_3(sK0)
    | ~ l1_pre_topc(sK0)
    | v1_xboole_0(sK2(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK2(sK0,sK1))
    | v2_struct_0(sK0) ),
    inference(resolution,[],[f79,f37])).

fof(f79,plain,
    ( v2_tex_2(sK2(sK0,sK1),sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f78,f34])).

fof(f78,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_tex_2(sK2(sK0,sK1),sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f71,f30])).

fof(f71,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v2_tex_2(sK2(sK0,sK1),sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f68,f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_tex_2(sK2(X0,X1),X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f147,plain,
    ( ~ v1_zfmisc_1(sK2(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(sK2(sK0,sK1)))
    | v1_xboole_0(sK2(sK0,sK1))
    | v1_xboole_0(sK1) ),
    inference(resolution,[],[f139,f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ~ v1_subset_1(X1,X0)
      | ~ v1_zfmisc_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_xboole_0(X0)
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_xboole_0(X1)
          | ~ v1_subset_1(X1,X0)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_zfmisc_1(X0)
        & ~ v1_xboole_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => ( v1_subset_1(X1,X0)
           => v1_xboole_0(X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tex_2)).

fof(f139,plain,(
    v1_subset_1(sK1,sK2(sK0,sK1)) ),
    inference(global_subsumption,[],[f28,f83,f91,f137])).

fof(f137,plain,
    ( sK1 = sK2(sK0,sK1)
    | v1_subset_1(sK1,sK2(sK0,sK1)) ),
    inference(resolution,[],[f135,f48])).

fof(f48,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | X0 = X1
      | v1_subset_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).

fof(f83,plain,
    ( sK1 != sK2(sK0,sK1)
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f82,f34])).

fof(f82,plain,
    ( ~ l1_pre_topc(sK0)
    | sK1 != sK2(sK0,sK1)
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f73,f30])).

fof(f73,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | sK1 != sK2(sK0,sK1)
    | v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f68,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v2_tex_2(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | sK2(X0,X1) != X1
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 10:50:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.49  % (2953)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.49  % (2954)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.49  % (2953)Refutation found. Thanks to Tanya!
% 0.21/0.49  % SZS status Theorem for theBenchmark
% 0.21/0.49  % SZS output start Proof for theBenchmark
% 0.21/0.49  fof(f151,plain,(
% 0.21/0.49    $false),
% 0.21/0.49    inference(subsumption_resolution,[],[f150,f29])).
% 0.21/0.49  fof(f29,plain,(
% 0.21/0.49    ~v1_xboole_0(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f13,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f12])).
% 0.21/0.49  fof(f12,plain,(
% 0.21/0.49    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f11])).
% 0.21/0.49  fof(f11,negated_conjecture,(
% 0.21/0.49    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.49    inference(negated_conjecture,[],[f10])).
% 0.21/0.49  fof(f10,conjecture,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).
% 0.21/0.49  fof(f150,plain,(
% 0.21/0.49    v1_xboole_0(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f149,f140])).
% 0.21/0.49  fof(f140,plain,(
% 0.21/0.49    ~v1_xboole_0(sK2(sK0,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f138,f29])).
% 0.21/0.49  fof(f138,plain,(
% 0.21/0.49    ~v1_xboole_0(sK2(sK0,sK1)) | v1_xboole_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f135,f45])).
% 0.21/0.49  fof(f45,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f21])).
% 0.21/0.49  fof(f21,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f2])).
% 0.21/0.49  fof(f2,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_xboole_0(X1)))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_subset_1)).
% 0.21/0.49  fof(f135,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(sK2(sK0,sK1)))),
% 0.21/0.49    inference(resolution,[],[f134,f50])).
% 0.21/0.49  fof(f50,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~r1_tarski(X0,X1) | m1_subset_1(X0,k1_zfmisc_1(X1))) )),
% 0.21/0.49    inference(cnf_transformation,[],[f3])).
% 0.21/0.49  fof(f3,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.21/0.49  fof(f134,plain,(
% 0.21/0.49    r1_tarski(sK1,sK2(sK0,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f132,f91])).
% 0.21/0.49  fof(f91,plain,(
% 0.21/0.49    v1_zfmisc_1(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f90,f31])).
% 0.21/0.49  fof(f31,plain,(
% 0.21/0.49    ~v2_struct_0(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f90,plain,(
% 0.21/0.49    v1_zfmisc_1(sK1) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f89,f30])).
% 0.21/0.49  fof(f30,plain,(
% 0.21/0.49    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f89,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(sK1) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f88,f29])).
% 0.21/0.49  fof(f88,plain,(
% 0.21/0.49    v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(sK1) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f87,f34])).
% 0.21/0.49  fof(f34,plain,(
% 0.21/0.49    l1_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f87,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(sK1) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f86,f33])).
% 0.21/0.49  fof(f33,plain,(
% 0.21/0.49    v2_tdlat_3(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f86,plain,(
% 0.21/0.49    ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(sK1) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f75,f32])).
% 0.21/0.49  fof(f32,plain,(
% 0.21/0.49    v2_pre_topc(sK0)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f75,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(sK1) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f68,f37])).
% 0.21/0.49  fof(f37,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v2_tex_2(X1,X0) | ~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_zfmisc_1(X1) | v2_struct_0(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f17,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.49    inference(flattening,[],[f16])).
% 0.21/0.49  fof(f16,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f9])).
% 0.21/0.49  fof(f9,axiom,(
% 0.21/0.49    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.21/0.49  fof(f68,plain,(
% 0.21/0.49    v2_tex_2(sK1,sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f67,f56])).
% 0.21/0.49  fof(f56,plain,(
% 0.21/0.49    v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f55,f34])).
% 0.21/0.49  fof(f55,plain,(
% 0.21/0.49    v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f54,f30])).
% 0.21/0.49  fof(f54,plain,(
% 0.21/0.49    v1_zfmisc_1(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.49    inference(resolution,[],[f27,f44])).
% 0.21/0.49  fof(f44,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v3_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f20,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(flattening,[],[f19])).
% 0.21/0.49  fof(f19,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f7])).
% 0.21/0.49  fof(f7,axiom,(
% 0.21/0.49    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 0.21/0.49  fof(f27,plain,(
% 0.21/0.49    v3_tex_2(sK1,sK0) | v1_zfmisc_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f67,plain,(
% 0.21/0.49    ~v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f66,f31])).
% 0.21/0.49  fof(f66,plain,(
% 0.21/0.49    v2_struct_0(sK0) | ~v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f65,f29])).
% 0.21/0.49  fof(f65,plain,(
% 0.21/0.49    v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f64,f34])).
% 0.21/0.49  fof(f64,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f63,f33])).
% 0.21/0.49  fof(f63,plain,(
% 0.21/0.49    ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f59,f32])).
% 0.21/0.49  fof(f59,plain,(
% 0.21/0.49    ~v2_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK1) | v2_struct_0(sK0) | ~v1_zfmisc_1(sK1) | v2_tex_2(sK1,sK0)),
% 0.21/0.49    inference(resolution,[],[f30,f36])).
% 0.21/0.49  fof(f36,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | v2_struct_0(X0) | ~v1_zfmisc_1(X1) | v2_tex_2(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f17])).
% 0.21/0.49  fof(f132,plain,(
% 0.21/0.49    r1_tarski(sK1,sK2(sK0,sK1)) | ~v1_zfmisc_1(sK1)),
% 0.21/0.49    inference(resolution,[],[f81,f28])).
% 0.21/0.49  fof(f28,plain,(
% 0.21/0.49    ~v3_tex_2(sK1,sK0) | ~v1_zfmisc_1(sK1)),
% 0.21/0.49    inference(cnf_transformation,[],[f13])).
% 0.21/0.49  fof(f81,plain,(
% 0.21/0.49    v3_tex_2(sK1,sK0) | r1_tarski(sK1,sK2(sK0,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f80,f34])).
% 0.21/0.49  fof(f80,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | r1_tarski(sK1,sK2(sK0,sK1)) | v3_tex_2(sK1,sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f72,f30])).
% 0.21/0.49  fof(f72,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | r1_tarski(sK1,sK2(sK0,sK1)) | v3_tex_2(sK1,sK0)),
% 0.21/0.49    inference(resolution,[],[f68,f41])).
% 0.21/0.49  fof(f41,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r1_tarski(X1,sK2(X0,X1)) | v3_tex_2(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f149,plain,(
% 0.21/0.49    v1_xboole_0(sK2(sK0,sK1)) | v1_xboole_0(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f148,f135])).
% 0.21/0.49  fof(f148,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(sK2(sK0,sK1))) | v1_xboole_0(sK2(sK0,sK1)) | v1_xboole_0(sK1)),
% 0.21/0.49    inference(subsumption_resolution,[],[f147,f131])).
% 0.21/0.49  fof(f131,plain,(
% 0.21/0.49    v1_zfmisc_1(sK2(sK0,sK1))),
% 0.21/0.49    inference(global_subsumption,[],[f28,f91,f130])).
% 0.21/0.49  fof(f130,plain,(
% 0.21/0.49    v3_tex_2(sK1,sK0) | v1_zfmisc_1(sK2(sK0,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f129,f77])).
% 0.21/0.49  fof(f77,plain,(
% 0.21/0.49    v3_tex_2(sK1,sK0) | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.49    inference(subsumption_resolution,[],[f76,f34])).
% 0.21/0.49  fof(f76,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(sK1,sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f70,f30])).
% 0.21/0.49  fof(f70,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tex_2(sK1,sK0)),
% 0.21/0.49    inference(resolution,[],[f68,f39])).
% 0.21/0.49  fof(f39,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_tex_2(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f129,plain,(
% 0.21/0.49    v3_tex_2(sK1,sK0) | ~m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(sK2(sK0,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f128,f38])).
% 0.21/0.49  fof(f38,plain,(
% 0.21/0.49    ( ! [X0] : (~v1_xboole_0(X0) | v1_zfmisc_1(X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f18])).
% 0.21/0.49  fof(f18,plain,(
% 0.21/0.49    ! [X0] : (v1_zfmisc_1(X0) | ~v1_xboole_0(X0))),
% 0.21/0.49    inference(ennf_transformation,[],[f1])).
% 0.21/0.49  fof(f1,axiom,(
% 0.21/0.49    ! [X0] : (v1_xboole_0(X0) => v1_zfmisc_1(X0))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_zfmisc_1)).
% 0.21/0.49  fof(f128,plain,(
% 0.21/0.49    v3_tex_2(sK1,sK0) | v1_xboole_0(sK2(sK0,sK1)) | ~m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(sK2(sK0,sK1))),
% 0.21/0.49    inference(subsumption_resolution,[],[f127,f31])).
% 0.21/0.49  fof(f127,plain,(
% 0.21/0.49    v3_tex_2(sK1,sK0) | v1_xboole_0(sK2(sK0,sK1)) | ~m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(sK2(sK0,sK1)) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f126,f34])).
% 0.21/0.49  fof(f126,plain,(
% 0.21/0.49    v3_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK2(sK0,sK1)) | ~m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(sK2(sK0,sK1)) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f125,f33])).
% 0.21/0.49  fof(f125,plain,(
% 0.21/0.49    v3_tex_2(sK1,sK0) | ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK2(sK0,sK1)) | ~m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(sK2(sK0,sK1)) | v2_struct_0(sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f109,f32])).
% 0.21/0.49  fof(f109,plain,(
% 0.21/0.49    v3_tex_2(sK1,sK0) | ~v2_pre_topc(sK0) | ~v2_tdlat_3(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(sK2(sK0,sK1)) | ~m1_subset_1(sK2(sK0,sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(sK2(sK0,sK1)) | v2_struct_0(sK0)),
% 0.21/0.49    inference(resolution,[],[f79,f37])).
% 0.21/0.49  fof(f79,plain,(
% 0.21/0.49    v2_tex_2(sK2(sK0,sK1),sK0) | v3_tex_2(sK1,sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f78,f34])).
% 0.21/0.49  fof(f78,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | v2_tex_2(sK2(sK0,sK1),sK0) | v3_tex_2(sK1,sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f71,f30])).
% 0.21/0.49  fof(f71,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_tex_2(sK2(sK0,sK1),sK0) | v3_tex_2(sK1,sK0)),
% 0.21/0.49    inference(resolution,[],[f68,f40])).
% 0.21/0.49  fof(f40,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_tex_2(sK2(X0,X1),X0) | v3_tex_2(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  fof(f147,plain,(
% 0.21/0.49    ~v1_zfmisc_1(sK2(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(sK2(sK0,sK1))) | v1_xboole_0(sK2(sK0,sK1)) | v1_xboole_0(sK1)),
% 0.21/0.49    inference(resolution,[],[f139,f35])).
% 0.21/0.49  fof(f35,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v1_subset_1(X1,X0) | ~v1_zfmisc_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_xboole_0(X0) | v1_xboole_0(X1)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f15])).
% 0.21/0.49  fof(f15,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : (v1_xboole_0(X1) | ~v1_subset_1(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_zfmisc_1(X0) | v1_xboole_0(X0))),
% 0.21/0.49    inference(flattening,[],[f14])).
% 0.21/0.49  fof(f14,plain,(
% 0.21/0.49    ! [X0] : (! [X1] : ((v1_xboole_0(X1) | ~v1_subset_1(X1,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | (~v1_zfmisc_1(X0) | v1_xboole_0(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f4])).
% 0.21/0.49  fof(f4,axiom,(
% 0.21/0.49    ! [X0] : ((v1_zfmisc_1(X0) & ~v1_xboole_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) => v1_xboole_0(X1))))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_tex_2)).
% 0.21/0.49  fof(f139,plain,(
% 0.21/0.49    v1_subset_1(sK1,sK2(sK0,sK1))),
% 0.21/0.49    inference(global_subsumption,[],[f28,f83,f91,f137])).
% 0.21/0.49  fof(f137,plain,(
% 0.21/0.49    sK1 = sK2(sK0,sK1) | v1_subset_1(sK1,sK2(sK0,sK1))),
% 0.21/0.49    inference(resolution,[],[f135,f48])).
% 0.21/0.49  fof(f48,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | X0 = X1 | v1_subset_1(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f26])).
% 0.21/0.49  fof(f26,plain,(
% 0.21/0.49    ! [X0,X1] : ((v1_subset_1(X1,X0) <=> X0 != X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 0.21/0.49    inference(ennf_transformation,[],[f6])).
% 0.21/0.49  fof(f6,axiom,(
% 0.21/0.49    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => (v1_subset_1(X1,X0) <=> X0 != X1))),
% 0.21/0.49    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_subset_1)).
% 0.21/0.49  fof(f83,plain,(
% 0.21/0.49    sK1 != sK2(sK0,sK1) | v3_tex_2(sK1,sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f82,f34])).
% 0.21/0.49  fof(f82,plain,(
% 0.21/0.49    ~l1_pre_topc(sK0) | sK1 != sK2(sK0,sK1) | v3_tex_2(sK1,sK0)),
% 0.21/0.49    inference(subsumption_resolution,[],[f73,f30])).
% 0.21/0.49  fof(f73,plain,(
% 0.21/0.49    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | sK1 != sK2(sK0,sK1) | v3_tex_2(sK1,sK0)),
% 0.21/0.49    inference(resolution,[],[f68,f42])).
% 0.21/0.49  fof(f42,plain,(
% 0.21/0.49    ( ! [X0,X1] : (~v2_tex_2(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | sK2(X0,X1) != X1 | v3_tex_2(X1,X0)) )),
% 0.21/0.49    inference(cnf_transformation,[],[f20])).
% 0.21/0.49  % SZS output end Proof for theBenchmark
% 0.21/0.49  % (2953)------------------------------
% 0.21/0.49  % (2953)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (2953)Termination reason: Refutation
% 0.21/0.49  
% 0.21/0.49  % (2953)Memory used [KB]: 6140
% 0.21/0.49  % (2953)Time elapsed: 0.090 s
% 0.21/0.49  % (2953)------------------------------
% 0.21/0.49  % (2953)------------------------------
% 0.21/0.50  % (2949)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.50  % (2958)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (2952)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (2954)Refutation not found, incomplete strategy% (2954)------------------------------
% 0.21/0.50  % (2954)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (2971)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.51  % (2947)Success in time 0.147 s
%------------------------------------------------------------------------------
