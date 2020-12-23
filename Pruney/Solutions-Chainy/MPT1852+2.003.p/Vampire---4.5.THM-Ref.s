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
% DateTime   : Thu Dec  3 13:20:40 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  113 (2744 expanded)
%              Number of leaves         :   11 ( 519 expanded)
%              Depth                    :   33
%              Number of atoms          :  307 (9844 expanded)
%              Number of equality atoms :   13 (1332 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f209,plain,(
    $false ),
    inference(subsumption_resolution,[],[f208,f191])).

fof(f191,plain,(
    m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f190,f90])).

fof(f90,plain,(
    ! [X0] :
      ( ~ r2_hidden(X0,u1_pre_topc(sK0))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f65,f51])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1)
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f65,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f35,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f35,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v3_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v3_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v3_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v3_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tex_2)).

fof(f190,plain,(
    r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f178,f186])).

fof(f186,plain,(
    r2_hidden(sK2(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f185,f35])).

fof(f185,plain,
    ( r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f184,f148])).

fof(f148,plain,(
    m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f62,f145])).

fof(f145,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f144,f137])).

fof(f137,plain,(
    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f132,f31])).

fof(f31,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f132,plain,
    ( ~ l1_pre_topc(sK1)
    | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(resolution,[],[f120,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(u1_struct_0(X1),u1_struct_0(X0))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).

fof(f120,plain,(
    m1_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f110,f35])).

fof(f110,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f88,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f77,f31])).

fof(f77,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,sK1) ) ),
    inference(superposition,[],[f45,f32])).

fof(f32,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f88,plain,(
    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f87,f35])).

fof(f87,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(duplicate_literal_removal,[],[f84])).

fof(f84,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f64,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f64,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(resolution,[],[f35,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f144,plain,
    ( ~ r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))
    | u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(resolution,[],[f128,f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | ~ r1_tarski(X1,X0)
      | X0 = X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f128,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f123,f35])).

fof(f123,plain,
    ( ~ l1_pre_topc(sK0)
    | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f107,f54])).

fof(f107,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f106,f31])).

fof(f106,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f99,f35])).

fof(f99,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | m1_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f76,f45])).

fof(f76,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(forward_demodulation,[],[f75,f32])).

fof(f75,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f74,f31])).

fof(f74,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(duplicate_literal_removal,[],[f71])).

fof(f71,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f58,f46])).

fof(f58,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(resolution,[],[f31,f50])).

fof(f62,plain,(
    m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f60,f34])).

fof(f34,plain,(
    ~ v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_tdlat_3(sK1) ),
    inference(resolution,[],[f31,f37])).

fof(f37,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_hidden(X1,u1_pre_topc(X0))
             => r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tdlat_3)).

fof(f184,plain,
    ( ~ m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f183,f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f183,plain,(
    v3_pre_topc(sK2(sK1),sK0) ),
    inference(subsumption_resolution,[],[f182,f148])).

fof(f182,plain,
    ( ~ m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2(sK1),sK0) ),
    inference(resolution,[],[f143,f95])).

fof(f95,plain,(
    v3_pre_topc(sK2(sK1),sK1) ),
    inference(subsumption_resolution,[],[f94,f63])).

fof(f63,plain,(
    r2_hidden(sK2(sK1),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f61,f34])).

fof(f61,plain,
    ( r2_hidden(sK2(sK1),u1_pre_topc(sK1))
    | v3_tdlat_3(sK1) ),
    inference(resolution,[],[f31,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | r2_hidden(sK2(X0),u1_pre_topc(X0))
      | v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f94,plain,
    ( ~ r2_hidden(sK2(sK1),u1_pre_topc(sK1))
    | v3_pre_topc(sK2(sK1),sK1) ),
    inference(subsumption_resolution,[],[f91,f31])).

fof(f91,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ r2_hidden(sK2(sK1),u1_pre_topc(sK1))
    | v3_pre_topc(sK2(sK1),sK1) ),
    inference(resolution,[],[f62,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f143,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f142,f138])).

fof(f138,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f134,f31])).

fof(f134,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(resolution,[],[f120,f48])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f142,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f136,f31])).

fof(f136,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X1,sK0) ) ),
    inference(resolution,[],[f120,f57])).

fof(f57,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(X3,X2) ) ),
    inference(equality_resolution,[],[f43])).

fof(f43,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | X1 != X3
      | v3_pre_topc(X3,X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( v3_pre_topc(X3,X2)
                  | X1 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) )
              | ~ v3_pre_topc(X1,X0)
              | ~ m1_pre_topc(X2,X0) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ! [X2] :
              ( m1_pre_topc(X2,X0)
             => ( v3_pre_topc(X1,X0)
               => ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
                   => ( X1 = X3
                     => v3_pre_topc(X3,X2) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).

fof(f178,plain,
    ( ~ r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f177,f33])).

fof(f33,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f177,plain,
    ( ~ r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | ~ v3_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f174,f35])).

fof(f174,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | ~ v3_tdlat_3(sK0) ),
    inference(resolution,[],[f148,f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
      | ~ v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f208,plain,(
    ~ m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f207,f145])).

fof(f207,plain,(
    ~ m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f206,f31])).

fof(f206,plain,
    ( ~ m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f205,f171])).

fof(f171,plain,(
    ~ r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f170,f34])).

fof(f170,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1))
    | v3_tdlat_3(sK1) ),
    inference(subsumption_resolution,[],[f163,f31])).

fof(f163,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | v3_tdlat_3(sK1) ),
    inference(superposition,[],[f39,f145])).

fof(f39,plain,(
    ! [X0] :
      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f205,plain,
    ( ~ m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f203,f53])).

fof(f203,plain,(
    v3_pre_topc(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),sK1) ),
    inference(subsumption_resolution,[],[f201,f191])).

fof(f201,plain,
    ( ~ m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),sK1) ),
    inference(resolution,[],[f197,f156])).

fof(f156,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X1,sK1) ) ),
    inference(backward_demodulation,[],[f131,f145])).

fof(f131,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | v3_pre_topc(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f130,f129])).

fof(f129,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f125,f35])).

fof(f125,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f107,f48])).

fof(f130,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | v3_pre_topc(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f127,f35])).

fof(f127,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | v3_pre_topc(X1,sK1) ) ),
    inference(resolution,[],[f107,f57])).

fof(f197,plain,(
    v3_pre_topc(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f196,f190])).

fof(f196,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | v3_pre_topc(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f193,f35])).

fof(f193,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | v3_pre_topc(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),sK0) ),
    inference(resolution,[],[f191,f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 19:14:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.44  % (26225)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.20/0.45  % (26240)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.20/0.46  % (26225)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % SZS output start Proof for theBenchmark
% 0.20/0.46  fof(f209,plain,(
% 0.20/0.46    $false),
% 0.20/0.46    inference(subsumption_resolution,[],[f208,f191])).
% 0.20/0.46  fof(f191,plain,(
% 0.20/0.46    m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.46    inference(resolution,[],[f190,f90])).
% 0.20/0.46  fof(f90,plain,(
% 0.20/0.46    ( ! [X0] : (~r2_hidden(X0,u1_pre_topc(sK0)) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.46    inference(resolution,[],[f65,f51])).
% 0.20/0.46  fof(f51,plain,(
% 0.20/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1) | m1_subset_1(X0,X2)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f28])).
% 0.20/0.46  fof(f28,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.20/0.46    inference(flattening,[],[f27])).
% 0.20/0.46  fof(f27,plain,(
% 0.20/0.46    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.20/0.46    inference(ennf_transformation,[],[f2])).
% 0.20/0.46  fof(f2,axiom,(
% 0.20/0.46    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.20/0.46  fof(f65,plain,(
% 0.20/0.46    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.20/0.46    inference(resolution,[],[f35,f47])).
% 0.20/0.46  fof(f47,plain,(
% 0.20/0.46    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f23])).
% 0.20/0.46  fof(f23,plain,(
% 0.20/0.46    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f5])).
% 0.20/0.46  fof(f5,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.20/0.46  fof(f35,plain,(
% 0.20/0.46    l1_pre_topc(sK0)),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f16,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.20/0.46    inference(flattening,[],[f15])).
% 0.20/0.46  fof(f15,plain,(
% 0.20/0.46    ? [X0] : (? [X1] : ((~v3_tdlat_3(X1) & (v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f14])).
% 0.20/0.46  fof(f14,negated_conjecture,(
% 0.20/0.46    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tdlat_3(X1))))),
% 0.20/0.46    inference(negated_conjecture,[],[f13])).
% 0.20/0.46  fof(f13,conjecture,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tdlat_3(X1))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tex_2)).
% 0.20/0.46  fof(f190,plain,(
% 0.20/0.46    r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))),
% 0.20/0.46    inference(resolution,[],[f178,f186])).
% 0.20/0.46  fof(f186,plain,(
% 0.20/0.46    r2_hidden(sK2(sK1),u1_pre_topc(sK0))),
% 0.20/0.46    inference(subsumption_resolution,[],[f185,f35])).
% 0.20/0.46  fof(f185,plain,(
% 0.20/0.46    r2_hidden(sK2(sK1),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f184,f148])).
% 0.20/0.46  fof(f148,plain,(
% 0.20/0.46    m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.46    inference(backward_demodulation,[],[f62,f145])).
% 0.20/0.46  fof(f145,plain,(
% 0.20/0.46    u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f144,f137])).
% 0.20/0.46  fof(f137,plain,(
% 0.20/0.46    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.46    inference(subsumption_resolution,[],[f132,f31])).
% 0.20/0.46  fof(f31,plain,(
% 0.20/0.46    l1_pre_topc(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f132,plain,(
% 0.20/0.46    ~l1_pre_topc(sK1) | r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.46    inference(resolution,[],[f120,f54])).
% 0.20/0.46  fof(f54,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | r1_tarski(u1_struct_0(X1),u1_struct_0(X0))) )),
% 0.20/0.46    inference(cnf_transformation,[],[f30])).
% 0.20/0.46  fof(f30,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : (r1_tarski(u1_struct_0(X1),u1_struct_0(X0)) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f11])).
% 0.20/0.46  fof(f11,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => r1_tarski(u1_struct_0(X1),u1_struct_0(X0))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_borsuk_1)).
% 0.20/0.46  fof(f120,plain,(
% 0.20/0.46    m1_pre_topc(sK0,sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f110,f35])).
% 0.20/0.46  fof(f110,plain,(
% 0.20/0.46    ~l1_pre_topc(sK0) | m1_pre_topc(sK0,sK1)),
% 0.20/0.46    inference(resolution,[],[f88,f79])).
% 0.20/0.46  fof(f79,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(X0) | m1_pre_topc(X0,sK1)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f77,f31])).
% 0.20/0.46  fof(f77,plain,(
% 0.20/0.46    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK1) | ~l1_pre_topc(X0) | m1_pre_topc(X0,sK1)) )),
% 0.20/0.46    inference(superposition,[],[f45,f32])).
% 0.20/0.46  fof(f32,plain,(
% 0.20/0.46    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f45,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_pre_topc(X0,X1)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f22])).
% 0.20/0.46  fof(f22,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f8])).
% 0.20/0.46  fof(f8,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.20/0.46  fof(f88,plain,(
% 0.20/0.46    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.20/0.46    inference(subsumption_resolution,[],[f87,f35])).
% 0.20/0.46  fof(f87,plain,(
% 0.20/0.46    ~l1_pre_topc(sK0) | m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.20/0.46    inference(duplicate_literal_removal,[],[f84])).
% 0.20/0.46  fof(f84,plain,(
% 0.20/0.46    ~l1_pre_topc(sK0) | m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0)),
% 0.20/0.46    inference(resolution,[],[f64,f46])).
% 0.20/0.46  fof(f46,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f22])).
% 0.20/0.46  fof(f64,plain,(
% 0.20/0.46    m1_pre_topc(sK0,sK0)),
% 0.20/0.46    inference(resolution,[],[f35,f50])).
% 0.20/0.46  fof(f50,plain,(
% 0.20/0.46    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f26])).
% 0.20/0.46  fof(f26,plain,(
% 0.20/0.46    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f10])).
% 0.20/0.46  fof(f10,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.20/0.46  fof(f144,plain,(
% 0.20/0.46    ~r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) | u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.20/0.46    inference(resolution,[],[f128,f42])).
% 0.20/0.46  fof(f42,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.20/0.46    inference(cnf_transformation,[],[f1])).
% 0.20/0.46  fof(f1,axiom,(
% 0.20/0.46    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.20/0.46  fof(f128,plain,(
% 0.20/0.46    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.46    inference(subsumption_resolution,[],[f123,f35])).
% 0.20/0.46  fof(f123,plain,(
% 0.20/0.46    ~l1_pre_topc(sK0) | r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.20/0.46    inference(resolution,[],[f107,f54])).
% 0.20/0.46  fof(f107,plain,(
% 0.20/0.46    m1_pre_topc(sK1,sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f106,f31])).
% 0.20/0.46  fof(f106,plain,(
% 0.20/0.46    ~l1_pre_topc(sK1) | m1_pre_topc(sK1,sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f99,f35])).
% 0.20/0.46  fof(f99,plain,(
% 0.20/0.46    ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | m1_pre_topc(sK1,sK0)),
% 0.20/0.46    inference(resolution,[],[f76,f45])).
% 0.20/0.46  fof(f76,plain,(
% 0.20/0.46    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.20/0.46    inference(forward_demodulation,[],[f75,f32])).
% 0.20/0.46  fof(f75,plain,(
% 0.20/0.46    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.20/0.46    inference(subsumption_resolution,[],[f74,f31])).
% 0.20/0.46  fof(f74,plain,(
% 0.20/0.46    ~l1_pre_topc(sK1) | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.20/0.46    inference(duplicate_literal_removal,[],[f71])).
% 0.20/0.46  fof(f71,plain,(
% 0.20/0.46    ~l1_pre_topc(sK1) | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1)),
% 0.20/0.46    inference(resolution,[],[f58,f46])).
% 0.20/0.46  fof(f58,plain,(
% 0.20/0.46    m1_pre_topc(sK1,sK1)),
% 0.20/0.46    inference(resolution,[],[f31,f50])).
% 0.20/0.46  fof(f62,plain,(
% 0.20/0.46    m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.46    inference(subsumption_resolution,[],[f60,f34])).
% 0.20/0.46  fof(f34,plain,(
% 0.20/0.46    ~v3_tdlat_3(sK1)),
% 0.20/0.46    inference(cnf_transformation,[],[f16])).
% 0.20/0.46  fof(f60,plain,(
% 0.20/0.46    m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | v3_tdlat_3(sK1)),
% 0.20/0.46    inference(resolution,[],[f31,f37])).
% 0.20/0.46  fof(f37,plain,(
% 0.20/0.46    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | v3_tdlat_3(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f18,plain,(
% 0.20/0.46    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(flattening,[],[f17])).
% 0.20/0.46  fof(f17,plain,(
% 0.20/0.46    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f12])).
% 0.20/0.46  fof(f12,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) => r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tdlat_3)).
% 0.20/0.46  fof(f184,plain,(
% 0.20/0.46    ~m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK2(sK1),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 0.20/0.46    inference(resolution,[],[f183,f53])).
% 0.20/0.46  fof(f53,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f29])).
% 0.20/0.46  fof(f29,plain,(
% 0.20/0.46    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.46    inference(ennf_transformation,[],[f3])).
% 0.20/0.46  fof(f3,axiom,(
% 0.20/0.46    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.20/0.46    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.20/0.46  fof(f183,plain,(
% 0.20/0.46    v3_pre_topc(sK2(sK1),sK0)),
% 0.20/0.46    inference(subsumption_resolution,[],[f182,f148])).
% 0.20/0.46  fof(f182,plain,(
% 0.20/0.46    ~m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK2(sK1),sK0)),
% 0.20/0.46    inference(resolution,[],[f143,f95])).
% 0.20/0.46  fof(f95,plain,(
% 0.20/0.46    v3_pre_topc(sK2(sK1),sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f94,f63])).
% 0.20/0.46  fof(f63,plain,(
% 0.20/0.46    r2_hidden(sK2(sK1),u1_pre_topc(sK1))),
% 0.20/0.46    inference(subsumption_resolution,[],[f61,f34])).
% 0.20/0.46  fof(f61,plain,(
% 0.20/0.46    r2_hidden(sK2(sK1),u1_pre_topc(sK1)) | v3_tdlat_3(sK1)),
% 0.20/0.46    inference(resolution,[],[f31,f38])).
% 0.20/0.46  fof(f38,plain,(
% 0.20/0.46    ( ! [X0] : (~l1_pre_topc(X0) | r2_hidden(sK2(X0),u1_pre_topc(X0)) | v3_tdlat_3(X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f18])).
% 0.20/0.46  fof(f94,plain,(
% 0.20/0.46    ~r2_hidden(sK2(sK1),u1_pre_topc(sK1)) | v3_pre_topc(sK2(sK1),sK1)),
% 0.20/0.46    inference(subsumption_resolution,[],[f91,f31])).
% 0.20/0.46  fof(f91,plain,(
% 0.20/0.46    ~l1_pre_topc(sK1) | ~r2_hidden(sK2(sK1),u1_pre_topc(sK1)) | v3_pre_topc(sK2(sK1),sK1)),
% 0.20/0.46    inference(resolution,[],[f62,f52])).
% 0.20/0.46  fof(f52,plain,(
% 0.20/0.46    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) )),
% 0.20/0.46    inference(cnf_transformation,[],[f29])).
% 0.20/0.46  fof(f143,plain,(
% 0.20/0.46    ( ! [X1] : (~v3_pre_topc(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X1,sK0)) )),
% 0.20/0.46    inference(subsumption_resolution,[],[f142,f138])).
% 0.20/0.47  fof(f138,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f134,f31])).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    ( ! [X0] : (~l1_pre_topc(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 0.20/0.47    inference(resolution,[],[f120,f48])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).
% 0.20/0.47  fof(f142,plain,(
% 0.20/0.47    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X1,sK0)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f136,f31])).
% 0.20/0.47  fof(f136,plain,(
% 0.20/0.47    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v3_pre_topc(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X1,sK0)) )),
% 0.20/0.47    inference(resolution,[],[f120,f57])).
% 0.20/0.47  fof(f57,plain,(
% 0.20/0.47    ( ! [X2,X0,X3] : (~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(X3,X2)) )),
% 0.20/0.47    inference(equality_resolution,[],[f43])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X2,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | X1 != X3 | v3_pre_topc(X3,X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(flattening,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).
% 0.20/0.47  fof(f178,plain,(
% 0.20/0.47    ~r2_hidden(sK2(sK1),u1_pre_topc(sK0)) | r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))),
% 0.20/0.47    inference(subsumption_resolution,[],[f177,f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    v3_tdlat_3(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f16])).
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    ~r2_hidden(sK2(sK1),u1_pre_topc(sK0)) | r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) | ~v3_tdlat_3(sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f174,f35])).
% 0.20/0.47  fof(f174,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | ~r2_hidden(sK2(sK1),u1_pre_topc(sK0)) | r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) | ~v3_tdlat_3(sK0)),
% 0.20/0.47    inference(resolution,[],[f148,f36])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~v3_tdlat_3(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f208,plain,(
% 0.20/0.47    ~m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.20/0.47    inference(forward_demodulation,[],[f207,f145])).
% 0.20/0.47  fof(f207,plain,(
% 0.20/0.47    ~m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.20/0.47    inference(subsumption_resolution,[],[f206,f31])).
% 0.20/0.47  fof(f206,plain,(
% 0.20/0.47    ~m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 0.20/0.47    inference(subsumption_resolution,[],[f205,f171])).
% 0.20/0.47  fof(f171,plain,(
% 0.20/0.47    ~r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1))),
% 0.20/0.47    inference(subsumption_resolution,[],[f170,f34])).
% 0.20/0.47  fof(f170,plain,(
% 0.20/0.47    ~r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1)) | v3_tdlat_3(sK1)),
% 0.20/0.47    inference(subsumption_resolution,[],[f163,f31])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    ~r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1)) | ~l1_pre_topc(sK1) | v3_tdlat_3(sK1)),
% 0.20/0.47    inference(superposition,[],[f39,f145])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0)) | ~l1_pre_topc(X0) | v3_tdlat_3(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f18])).
% 0.20/0.47  fof(f205,plain,(
% 0.20/0.47    ~m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK1))) | r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1)) | ~l1_pre_topc(sK1)),
% 0.20/0.47    inference(resolution,[],[f203,f53])).
% 0.20/0.47  fof(f203,plain,(
% 0.20/0.47    v3_pre_topc(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),sK1)),
% 0.20/0.47    inference(subsumption_resolution,[],[f201,f191])).
% 0.20/0.47  fof(f201,plain,(
% 0.20/0.47    ~m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),sK1)),
% 0.20/0.47    inference(resolution,[],[f197,f156])).
% 0.20/0.47  fof(f156,plain,(
% 0.20/0.47    ( ! [X1] : (~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X1,sK1)) )),
% 0.20/0.47    inference(backward_demodulation,[],[f131,f145])).
% 0.20/0.47  fof(f131,plain,(
% 0.20/0.47    ( ! [X1] : (~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(X1,sK1)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f130,f129])).
% 0.20/0.47  fof(f129,plain,(
% 0.20/0.47    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f125,f35])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 0.20/0.47    inference(resolution,[],[f107,f48])).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(X1,sK1)) )),
% 0.20/0.47    inference(subsumption_resolution,[],[f127,f35])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(X1,sK1)) )),
% 0.20/0.47    inference(resolution,[],[f107,f57])).
% 0.20/0.47  fof(f197,plain,(
% 0.20/0.47    v3_pre_topc(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f196,f190])).
% 0.20/0.47  fof(f196,plain,(
% 0.20/0.47    ~r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) | v3_pre_topc(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),sK0)),
% 0.20/0.47    inference(subsumption_resolution,[],[f193,f35])).
% 0.20/0.47  fof(f193,plain,(
% 0.20/0.47    ~l1_pre_topc(sK0) | ~r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) | v3_pre_topc(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),sK0)),
% 0.20/0.47    inference(resolution,[],[f191,f52])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.47  % (26225)------------------------------
% 0.20/0.47  % (26225)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (26225)Termination reason: Refutation
% 0.20/0.47  
% 0.20/0.47  % (26225)Memory used [KB]: 6140
% 0.20/0.47  % (26225)Time elapsed: 0.077 s
% 0.20/0.47  % (26225)------------------------------
% 0.20/0.47  % (26225)------------------------------
% 0.20/0.47  % (26219)Success in time 0.116 s
%------------------------------------------------------------------------------
