%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:22:05 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 848 expanded)
%              Number of leaves         :    8 ( 146 expanded)
%              Depth                    :   38
%              Number of atoms          :  346 (5177 expanded)
%              Number of equality atoms :   24 (  61 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f200,plain,(
    $false ),
    inference(subsumption_resolution,[],[f199,f94])).

fof(f94,plain,(
    ~ v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f92,f24])).

fof(f24,plain,
    ( ~ v1_zfmisc_1(sK1)
    | ~ v3_tex_2(sK1,sK0) ),
    inference(cnf_transformation,[],[f12])).

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
    inference(flattening,[],[f11])).

fof(f11,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,negated_conjecture,(
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
    inference(negated_conjecture,[],[f9])).

fof(f9,conjecture,(
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

fof(f92,plain,(
    v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f91,f25])).

fof(f25,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f91,plain,
    ( v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1) ),
    inference(subsumption_resolution,[],[f90,f26])).

fof(f26,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f90,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK1)
    | v1_xboole_0(sK1)
    | v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f87,f64])).

fof(f64,plain,
    ( v2_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1) ),
    inference(subsumption_resolution,[],[f63,f26])).

fof(f63,plain,
    ( v2_tex_2(sK1,sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK1) ),
    inference(resolution,[],[f62,f23])).

fof(f23,plain,
    ( v3_tex_2(sK1,sK0)
    | v1_zfmisc_1(sK1) ),
    inference(cnf_transformation,[],[f12])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v3_tex_2(X0,sK0)
      | v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f37,f30])).

fof(f30,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_tex_2(X1,X0)
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
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
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

fof(f87,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_zfmisc_1(X0)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f86,f30])).

fof(f86,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_zfmisc_1(X0)
      | ~ v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f85,f27])).

fof(f27,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f85,plain,(
    ! [X0] :
      ( v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_zfmisc_1(X0)
      | ~ v2_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f84,f28])).

fof(f28,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | v2_struct_0(sK0)
      | ~ l1_pre_topc(sK0)
      | v1_xboole_0(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_zfmisc_1(X0)
      | ~ v2_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f39,f29])).

fof(f29,plain,(
    v2_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f12])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_zfmisc_1(X1)
      | ~ v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f199,plain,(
    v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f198,f30])).

fof(f198,plain,
    ( ~ l1_pre_topc(sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f197,f105])).

fof(f105,plain,(
    v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f104,f27])).

fof(f104,plain,
    ( v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f103,f26])).

fof(f103,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f102,f30])).

fof(f102,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f101,f28])).

fof(f101,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | v2_tex_2(sK1,sK0) ),
    inference(resolution,[],[f97,f29])).

fof(f97,plain,(
    ! [X0] :
      ( ~ v2_tdlat_3(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | v2_tex_2(sK1,X0) ) ),
    inference(subsumption_resolution,[],[f95,f25])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(sK1)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | v2_tex_2(sK1,X0) ) ),
    inference(resolution,[],[f92,f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | ~ v2_pre_topc(X0)
      | ~ v2_tdlat_3(X0)
      | ~ l1_pre_topc(X0)
      | v1_xboole_0(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | v2_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f197,plain,
    ( ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f195,f26])).

fof(f195,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(trivial_inequality_removal,[],[f193])).

fof(f193,plain,
    ( sK1 != sK1
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v2_tex_2(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v3_tex_2(sK1,sK0) ),
    inference(superposition,[],[f35,f172])).

fof(f172,plain,(
    sK1 = sK2(sK0,sK1) ),
    inference(duplicate_literal_removal,[],[f159])).

fof(f159,plain,
    ( sK1 = sK2(sK0,sK1)
    | sK1 = sK2(sK0,sK1) ),
    inference(resolution,[],[f156,f112])).

fof(f112,plain,
    ( ~ r1_tarski(sK2(sK0,sK1),sK1)
    | sK1 = sK2(sK0,sK1) ),
    inference(resolution,[],[f109,f43])).

fof(f43,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f109,plain,(
    r1_tarski(sK1,sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f108,f94])).

fof(f108,plain,
    ( r1_tarski(sK1,sK2(sK0,sK1))
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f107,f26])).

fof(f107,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | r1_tarski(sK1,sK2(sK0,sK1))
    | v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f105,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | r1_tarski(X0,sK2(sK0,X0))
      | v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f34,f30])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | r1_tarski(X1,sK2(X0,X1))
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f156,plain,(
    ! [X0] :
      ( r1_tarski(sK2(sK0,sK1),X0)
      | sK1 = sK2(sK0,sK1) ) ),
    inference(resolution,[],[f142,f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( r2_hidden(sK3(X0,X1),X0)
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X1)
          | ~ r2_hidden(X2,X0) ) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
    <=> ! [X2] :
          ( r2_hidden(X2,X0)
         => r2_hidden(X2,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

fof(f142,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,sK2(sK0,sK1))
      | sK1 = sK2(sK0,sK1) ) ),
    inference(resolution,[],[f141,f50])).

fof(f50,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f2])).

fof(f141,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,sK2(sK0,sK1))
      | ~ r2_hidden(X0,X1)
      | sK1 = sK2(sK0,sK1) ) ),
    inference(resolution,[],[f140,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).

fof(f140,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(sK2(sK0,sK1)))
      | sK1 = sK2(sK0,sK1)
      | ~ r2_hidden(X2,X1) ) ),
    inference(resolution,[],[f138,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ~ v1_xboole_0(X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ~ ( v1_xboole_0(X2)
        & m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).

fof(f138,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | sK1 = sK2(sK0,sK1) ),
    inference(subsumption_resolution,[],[f136,f25])).

fof(f136,plain,
    ( v1_xboole_0(sK1)
    | v1_xboole_0(sK2(sK0,sK1))
    | sK1 = sK2(sK0,sK1) ),
    inference(resolution,[],[f132,f109])).

fof(f132,plain,(
    ! [X1] :
      ( ~ r1_tarski(X1,sK2(sK0,sK1))
      | v1_xboole_0(X1)
      | v1_xboole_0(sK2(sK0,sK1))
      | sK2(sK0,sK1) = X1 ) ),
    inference(duplicate_literal_removal,[],[f131])).

fof(f131,plain,(
    ! [X1] :
      ( v1_xboole_0(sK2(sK0,sK1))
      | v1_xboole_0(sK2(sK0,sK1))
      | v1_xboole_0(X1)
      | ~ r1_tarski(X1,sK2(sK0,sK1))
      | sK2(sK0,sK1) = X1 ) ),
    inference(resolution,[],[f128,f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ~ v1_zfmisc_1(X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0)
      | ~ r1_tarski(X0,X1)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f13])).

fof(f13,plain,(
    ! [X0] :
      ( ! [X1] :
          ( X0 = X1
          | ~ r1_tarski(X0,X1)
          | ~ v1_zfmisc_1(X1)
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ( v1_zfmisc_1(X1)
            & ~ v1_xboole_0(X1) )
         => ( r1_tarski(X0,X1)
           => X0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).

fof(f128,plain,
    ( v1_zfmisc_1(sK2(sK0,sK1))
    | v1_xboole_0(sK2(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f127,f94])).

fof(f127,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | v1_zfmisc_1(sK2(sK0,sK1))
    | v3_tex_2(sK1,sK0) ),
    inference(subsumption_resolution,[],[f124,f26])).

fof(f124,plain,
    ( v1_xboole_0(sK2(sK0,sK1))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v1_zfmisc_1(sK2(sK0,sK1))
    | v3_tex_2(sK1,sK0) ),
    inference(resolution,[],[f122,f105])).

fof(f122,plain,(
    ! [X0] :
      ( ~ v2_tex_2(X0,sK0)
      | v1_xboole_0(sK2(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_zfmisc_1(sK2(sK0,X0))
      | v3_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f121,f30])).

fof(f121,plain,(
    ! [X0] :
      ( v1_zfmisc_1(sK2(sK0,X0))
      | v1_xboole_0(sK2(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v3_tex_2(X0,sK0)
      | ~ l1_pre_topc(sK0) ) ),
    inference(duplicate_literal_removal,[],[f119])).

fof(f119,plain,(
    ! [X0] :
      ( v1_zfmisc_1(sK2(sK0,X0))
      | v1_xboole_0(sK2(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v3_tex_2(X0,sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f93,f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f93,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_zfmisc_1(sK2(sK0,X0))
      | v1_xboole_0(sK2(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | v3_tex_2(X0,sK0) ) ),
    inference(subsumption_resolution,[],[f89,f30])).

fof(f89,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_zfmisc_1(sK2(sK0,X0))
      | v1_xboole_0(sK2(sK0,X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v2_tex_2(X0,sK0)
      | ~ l1_pre_topc(sK0)
      | v3_tex_2(X0,sK0) ) ),
    inference(resolution,[],[f87,f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( v2_tex_2(sK2(X0,X1),X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f35,plain,(
    ! [X0,X1] :
      ( sK2(X0,X1) != X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_tex_2(X1,X0)
      | ~ l1_pre_topc(X0)
      | v3_tex_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:34:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.47  % (23994)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.47  % (23986)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.48  % (23986)Refutation found. Thanks to Tanya!
% 0.20/0.48  % SZS status Theorem for theBenchmark
% 0.20/0.48  % SZS output start Proof for theBenchmark
% 0.20/0.48  fof(f200,plain,(
% 0.20/0.48    $false),
% 0.20/0.48    inference(subsumption_resolution,[],[f199,f94])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    ~v3_tex_2(sK1,sK0)),
% 0.20/0.48    inference(resolution,[],[f92,f24])).
% 0.20/0.48  fof(f24,plain,(
% 0.20/0.48    ~v1_zfmisc_1(sK1) | ~v3_tex_2(sK1,sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) & l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f11])).
% 0.20/0.48  fof(f11,plain,(
% 0.20/0.48    ? [X0] : (? [X1] : ((v3_tex_2(X1,X0) <~> v1_zfmisc_1(X1)) & (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1))) & (l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f10])).
% 0.20/0.48  fof(f10,negated_conjecture,(
% 0.20/0.48    ~! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.20/0.48    inference(negated_conjecture,[],[f9])).
% 0.20/0.48  fof(f9,conjecture,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v3_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_tex_2)).
% 0.20/0.48  fof(f92,plain,(
% 0.20/0.48    v1_zfmisc_1(sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f91,f25])).
% 0.20/0.48  fof(f25,plain,(
% 0.20/0.48    ~v1_xboole_0(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f91,plain,(
% 0.20/0.48    v1_zfmisc_1(sK1) | v1_xboole_0(sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f90,f26])).
% 0.20/0.48  fof(f26,plain,(
% 0.20/0.48    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(sK1) | v1_xboole_0(sK1)),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f88])).
% 0.20/0.48  fof(f88,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(sK1) | v1_xboole_0(sK1) | v1_zfmisc_1(sK1)),
% 0.20/0.48    inference(resolution,[],[f87,f64])).
% 0.20/0.48  fof(f64,plain,(
% 0.20/0.48    v2_tex_2(sK1,sK0) | v1_zfmisc_1(sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f63,f26])).
% 0.20/0.48  fof(f63,plain,(
% 0.20/0.48    v2_tex_2(sK1,sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(sK1)),
% 0.20/0.48    inference(resolution,[],[f62,f23])).
% 0.20/0.48  fof(f23,plain,(
% 0.20/0.48    v3_tex_2(sK1,sK0) | v1_zfmisc_1(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f62,plain,(
% 0.20/0.48    ( ! [X0] : (~v3_tex_2(X0,sK0) | v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.48    inference(resolution,[],[f37,f30])).
% 0.20/0.48  fof(f30,plain,(
% 0.20/0.48    l1_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_tex_2(X1,X0) | ~v3_tex_2(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f16,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : (X1 = X2 | ~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(flattening,[],[f15])).
% 0.20/0.48  fof(f15,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((v3_tex_2(X1,X0) <=> (! [X2] : ((X1 = X2 | (~r1_tarski(X1,X2) | ~v2_tex_2(X2,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & v2_tex_2(X1,X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f5])).
% 0.20/0.48  fof(f5,axiom,(
% 0.20/0.48    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_tex_2(X1,X0) <=> (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => ((r1_tarski(X1,X2) & v2_tex_2(X2,X0)) => X1 = X2)) & v2_tex_2(X1,X0)))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_tex_2)).
% 0.20/0.48  fof(f87,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(X0) | v1_xboole_0(X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f86,f30])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    ( ! [X0] : (~l1_pre_topc(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(X0) | ~v2_tex_2(X0,sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f85,f27])).
% 0.20/0.48  fof(f27,plain,(
% 0.20/0.48    ~v2_struct_0(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f85,plain,(
% 0.20/0.48    ( ! [X0] : (v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(X0) | ~v2_tex_2(X0,sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f84,f28])).
% 0.20/0.48  fof(f28,plain,(
% 0.20/0.48    v2_pre_topc(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f84,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_pre_topc(sK0) | v2_struct_0(sK0) | ~l1_pre_topc(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(X0) | ~v2_tex_2(X0,sK0)) )),
% 0.20/0.48    inference(resolution,[],[f39,f29])).
% 0.20/0.48  fof(f29,plain,(
% 0.20/0.48    v2_tdlat_3(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f12])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_zfmisc_1(X1) | ~v2_tex_2(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1)) | ~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f17])).
% 0.20/0.48  fof(f17,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1)) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_xboole_0(X1))) | (~l1_pre_topc(X0) | ~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f8])).
% 0.20/0.48  fof(f8,axiom,(
% 0.20/0.48    ! [X0] : ((l1_pre_topc(X0) & v2_tdlat_3(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & ~v1_xboole_0(X1)) => (v2_tex_2(X1,X0) <=> v1_zfmisc_1(X1))))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_tex_2)).
% 0.20/0.48  fof(f199,plain,(
% 0.20/0.48    v3_tex_2(sK1,sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f198,f30])).
% 0.20/0.48  fof(f198,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | v3_tex_2(sK1,sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f197,f105])).
% 0.20/0.48  fof(f105,plain,(
% 0.20/0.48    v2_tex_2(sK1,sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f104,f27])).
% 0.20/0.48  fof(f104,plain,(
% 0.20/0.48    v2_struct_0(sK0) | v2_tex_2(sK1,sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f103,f26])).
% 0.20/0.48  fof(f103,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | v2_tex_2(sK1,sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f102,f30])).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | v2_tex_2(sK1,sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f101,f28])).
% 0.20/0.48  fof(f101,plain,(
% 0.20/0.48    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | v2_tex_2(sK1,sK0)),
% 0.20/0.48    inference(resolution,[],[f97,f29])).
% 0.20/0.48  fof(f97,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_tdlat_3(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | v2_tex_2(sK1,X0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f95,f25])).
% 0.20/0.48  fof(f95,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v1_xboole_0(sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | v2_tex_2(sK1,X0)) )),
% 0.20/0.48    inference(resolution,[],[f92,f38])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | ~v2_pre_topc(X0) | ~v2_tdlat_3(X0) | ~l1_pre_topc(X0) | v1_xboole_0(X1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | v2_tex_2(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f197,plain,(
% 0.20/0.48    ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | v3_tex_2(sK1,sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f195,f26])).
% 0.20/0.48  fof(f195,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | v3_tex_2(sK1,sK0)),
% 0.20/0.48    inference(trivial_inequality_removal,[],[f193])).
% 0.20/0.48  fof(f193,plain,(
% 0.20/0.48    sK1 != sK1 | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(sK1,sK0) | ~l1_pre_topc(sK0) | v3_tex_2(sK1,sK0)),
% 0.20/0.48    inference(superposition,[],[f35,f172])).
% 0.20/0.48  fof(f172,plain,(
% 0.20/0.48    sK1 = sK2(sK0,sK1)),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f159])).
% 0.20/0.48  fof(f159,plain,(
% 0.20/0.48    sK1 = sK2(sK0,sK1) | sK1 = sK2(sK0,sK1)),
% 0.20/0.48    inference(resolution,[],[f156,f112])).
% 0.20/0.48  fof(f112,plain,(
% 0.20/0.48    ~r1_tarski(sK2(sK0,sK1),sK1) | sK1 = sK2(sK0,sK1)),
% 0.20/0.48    inference(resolution,[],[f109,f43])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.48  fof(f109,plain,(
% 0.20/0.48    r1_tarski(sK1,sK2(sK0,sK1))),
% 0.20/0.48    inference(subsumption_resolution,[],[f108,f94])).
% 0.20/0.48  fof(f108,plain,(
% 0.20/0.48    r1_tarski(sK1,sK2(sK0,sK1)) | v3_tex_2(sK1,sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f107,f26])).
% 0.20/0.48  fof(f107,plain,(
% 0.20/0.48    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(sK1,sK2(sK0,sK1)) | v3_tex_2(sK1,sK0)),
% 0.20/0.48    inference(resolution,[],[f105,f72])).
% 0.20/0.48  fof(f72,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | r1_tarski(X0,sK2(sK0,X0)) | v3_tex_2(X0,sK0)) )),
% 0.20/0.48    inference(resolution,[],[f34,f30])).
% 0.20/0.48  fof(f34,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | r1_tarski(X1,sK2(X0,X1)) | v3_tex_2(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f156,plain,(
% 0.20/0.48    ( ! [X0] : (r1_tarski(sK2(sK0,sK1),X0) | sK1 = sK2(sK0,sK1)) )),
% 0.20/0.48    inference(resolution,[],[f142,f45])).
% 0.20/0.48  fof(f45,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r2_hidden(sK3(X0,X1),X0) | r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X1) | ~r2_hidden(X2,X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    ! [X0,X1] : (r1_tarski(X0,X1) <=> ! [X2] : (r2_hidden(X2,X0) => r2_hidden(X2,X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).
% 0.20/0.48  fof(f142,plain,(
% 0.20/0.48    ( ! [X0] : (~r2_hidden(X0,sK2(sK0,sK1)) | sK1 = sK2(sK0,sK1)) )),
% 0.20/0.48    inference(resolution,[],[f141,f50])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.20/0.48    inference(equality_resolution,[],[f42])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f2])).
% 0.20/0.48  fof(f141,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~r1_tarski(X1,sK2(sK0,sK1)) | ~r2_hidden(X0,X1) | sK1 = sK2(sK0,sK1)) )),
% 0.20/0.48    inference(resolution,[],[f140,f47])).
% 0.20/0.48  fof(f47,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) | ~r1_tarski(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_subset)).
% 0.20/0.48  fof(f140,plain,(
% 0.20/0.48    ( ! [X2,X1] : (~m1_subset_1(X1,k1_zfmisc_1(sK2(sK0,sK1))) | sK1 = sK2(sK0,sK1) | ~r2_hidden(X2,X1)) )),
% 0.20/0.48    inference(resolution,[],[f138,f49])).
% 0.20/0.48  fof(f49,plain,(
% 0.20/0.48    ( ! [X2,X0,X1] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f22])).
% 0.20/0.48  fof(f22,plain,(
% 0.20/0.48    ! [X0,X1,X2] : (~v1_xboole_0(X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.48    inference(ennf_transformation,[],[f4])).
% 0.20/0.48  fof(f4,axiom,(
% 0.20/0.48    ! [X0,X1,X2] : ~(v1_xboole_0(X2) & m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_subset)).
% 0.20/0.48  fof(f138,plain,(
% 0.20/0.48    v1_xboole_0(sK2(sK0,sK1)) | sK1 = sK2(sK0,sK1)),
% 0.20/0.48    inference(subsumption_resolution,[],[f136,f25])).
% 0.20/0.48  fof(f136,plain,(
% 0.20/0.48    v1_xboole_0(sK1) | v1_xboole_0(sK2(sK0,sK1)) | sK1 = sK2(sK0,sK1)),
% 0.20/0.48    inference(resolution,[],[f132,f109])).
% 0.20/0.48  fof(f132,plain,(
% 0.20/0.48    ( ! [X1] : (~r1_tarski(X1,sK2(sK0,sK1)) | v1_xboole_0(X1) | v1_xboole_0(sK2(sK0,sK1)) | sK2(sK0,sK1) = X1) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f131])).
% 0.20/0.48  fof(f131,plain,(
% 0.20/0.48    ( ! [X1] : (v1_xboole_0(sK2(sK0,sK1)) | v1_xboole_0(sK2(sK0,sK1)) | v1_xboole_0(X1) | ~r1_tarski(X1,sK2(sK0,sK1)) | sK2(sK0,sK1) = X1) )),
% 0.20/0.48    inference(resolution,[],[f128,f31])).
% 0.20/0.48  fof(f31,plain,(
% 0.20/0.48    ( ! [X0,X1] : (~v1_zfmisc_1(X1) | v1_xboole_0(X1) | v1_xboole_0(X0) | ~r1_tarski(X0,X1) | X0 = X1) )),
% 0.20/0.48    inference(cnf_transformation,[],[f14])).
% 0.20/0.48  fof(f14,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (X0 = X1 | ~r1_tarski(X0,X1) | ~v1_zfmisc_1(X1) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.48    inference(flattening,[],[f13])).
% 0.20/0.48  fof(f13,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : ((X0 = X1 | ~r1_tarski(X0,X1)) | (~v1_zfmisc_1(X1) | v1_xboole_0(X1))) | v1_xboole_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f6])).
% 0.20/0.48  fof(f6,axiom,(
% 0.20/0.48    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : ((v1_zfmisc_1(X1) & ~v1_xboole_0(X1)) => (r1_tarski(X0,X1) => X0 = X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_tex_2)).
% 0.20/0.48  fof(f128,plain,(
% 0.20/0.48    v1_zfmisc_1(sK2(sK0,sK1)) | v1_xboole_0(sK2(sK0,sK1))),
% 0.20/0.48    inference(subsumption_resolution,[],[f127,f94])).
% 0.20/0.48  fof(f127,plain,(
% 0.20/0.48    v1_xboole_0(sK2(sK0,sK1)) | v1_zfmisc_1(sK2(sK0,sK1)) | v3_tex_2(sK1,sK0)),
% 0.20/0.48    inference(subsumption_resolution,[],[f124,f26])).
% 0.20/0.48  fof(f124,plain,(
% 0.20/0.48    v1_xboole_0(sK2(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(sK2(sK0,sK1)) | v3_tex_2(sK1,sK0)),
% 0.20/0.48    inference(resolution,[],[f122,f105])).
% 0.20/0.48  fof(f122,plain,(
% 0.20/0.48    ( ! [X0] : (~v2_tex_2(X0,sK0) | v1_xboole_0(sK2(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(sK2(sK0,X0)) | v3_tex_2(X0,sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f121,f30])).
% 0.20/0.48  fof(f121,plain,(
% 0.20/0.48    ( ! [X0] : (v1_zfmisc_1(sK2(sK0,X0)) | v1_xboole_0(sK2(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v3_tex_2(X0,sK0) | ~l1_pre_topc(sK0)) )),
% 0.20/0.48    inference(duplicate_literal_removal,[],[f119])).
% 0.20/0.48  fof(f119,plain,(
% 0.20/0.48    ( ! [X0] : (v1_zfmisc_1(sK2(sK0,X0)) | v1_xboole_0(sK2(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v3_tex_2(X0,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~l1_pre_topc(sK0) | v3_tex_2(X0,sK0)) )),
% 0.20/0.48    inference(resolution,[],[f93,f32])).
% 0.20/0.48  fof(f32,plain,(
% 0.20/0.48    ( ! [X0,X1] : (m1_subset_1(sK2(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~l1_pre_topc(X0) | v3_tex_2(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f93,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(sK2(sK0,X0)) | v1_xboole_0(sK2(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | v3_tex_2(X0,sK0)) )),
% 0.20/0.48    inference(subsumption_resolution,[],[f89,f30])).
% 0.20/0.48  fof(f89,plain,(
% 0.20/0.48    ( ! [X0] : (~m1_subset_1(sK2(sK0,X0),k1_zfmisc_1(u1_struct_0(sK0))) | v1_zfmisc_1(sK2(sK0,X0)) | v1_xboole_0(sK2(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~v2_tex_2(X0,sK0) | ~l1_pre_topc(sK0) | v3_tex_2(X0,sK0)) )),
% 0.20/0.48    inference(resolution,[],[f87,f33])).
% 0.20/0.48  fof(f33,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v2_tex_2(sK2(X0,X1),X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~l1_pre_topc(X0) | v3_tex_2(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    ( ! [X0,X1] : (sK2(X0,X1) != X1 | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_tex_2(X1,X0) | ~l1_pre_topc(X0) | v3_tex_2(X1,X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f16])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (23986)------------------------------
% 0.20/0.48  % (23986)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (23986)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (23986)Memory used [KB]: 6268
% 0.20/0.48  % (23986)Time elapsed: 0.013 s
% 0.20/0.48  % (23986)------------------------------
% 0.20/0.48  % (23986)------------------------------
% 0.20/0.48  % (23979)Success in time 0.13 s
%------------------------------------------------------------------------------
