%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:20:40 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.33s
% Verified   : 
% Statistics : Number of formulae       :  117 (2834 expanded)
%              Number of leaves         :   12 ( 549 expanded)
%              Depth                    :   35
%              Number of atoms          :  313 (9994 expanded)
%              Number of equality atoms :   13 (1332 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f231,plain,(
    $false ),
    inference(subsumption_resolution,[],[f230,f216])).

fof(f216,plain,(
    m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f210,f68])).

fof(f68,plain,(
    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0)))) ),
    inference(resolution,[],[f36,f48])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).

fof(f36,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ~ v3_tdlat_3(X1)
          & v3_tdlat_3(X0)
          & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))
          & l1_pre_topc(X1) )
      & l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_pre_topc(X0)
       => ! [X1] :
            ( l1_pre_topc(X1)
           => ( ( v3_tdlat_3(X0)
                & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
             => v3_tdlat_3(X1) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( ( v3_tdlat_3(X0)
              & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) )
           => v3_tdlat_3(X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tex_2)).

fof(f210,plain,(
    ! [X0] :
      ( ~ m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(X0))
      | m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),X0) ) ),
    inference(resolution,[],[f207,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ r2_hidden(X0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | m1_subset_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X0,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X2))
      | ~ r2_hidden(X0,X1) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(X2))
        & r2_hidden(X0,X1) )
     => m1_subset_1(X0,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).

fof(f207,plain,(
    r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f206,f34])).

fof(f34,plain,(
    v3_tdlat_3(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f206,plain,
    ( r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | ~ v3_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f205,f36])).

fof(f205,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | ~ v3_tdlat_3(sK0) ),
    inference(subsumption_resolution,[],[f203,f164])).

fof(f164,plain,(
    m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f65,f161])).

fof(f161,plain,(
    u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(subsumption_resolution,[],[f160,f151])).

fof(f151,plain,(
    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) ),
    inference(resolution,[],[f122,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).

fof(f122,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f118,f36])).

fof(f118,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f114,f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f114,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f113,f32])).

fof(f32,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f113,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f106,f36])).

fof(f106,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(sK1)
    | m1_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f80,f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X1) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ( m1_pre_topc(X0,X1)
          <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).

fof(f80,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(forward_demodulation,[],[f79,f33])).

fof(f33,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f79,plain,(
    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(subsumption_resolution,[],[f77,f32])).

fof(f77,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) ),
    inference(duplicate_literal_removal,[],[f74])).

fof(f74,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f61,f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X0,X1)
      | ~ l1_pre_topc(X1)
      | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f61,plain,(
    m1_pre_topc(sK1,sK1) ),
    inference(resolution,[],[f32,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( m1_pre_topc(X0,X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => m1_pre_topc(X0,X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).

fof(f160,plain,
    ( ~ r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))
    | u1_struct_0(sK0) = u1_struct_0(sK1) ),
    inference(resolution,[],[f156,f43])).

fof(f43,plain,(
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

fof(f156,plain,(
    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(resolution,[],[f144,f57])).

fof(f144,plain,(
    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f140,f32])).

fof(f140,plain,
    ( ~ l1_pre_topc(sK1)
    | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(resolution,[],[f136,f50])).

fof(f136,plain,(
    m1_pre_topc(sK0,sK1) ),
    inference(subsumption_resolution,[],[f126,f36])).

fof(f126,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK0,sK1) ),
    inference(resolution,[],[f93,f83])).

fof(f83,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,sK1) ) ),
    inference(subsumption_resolution,[],[f81,f32])).

fof(f81,plain,(
    ! [X0] :
      ( ~ m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ l1_pre_topc(sK1)
      | ~ l1_pre_topc(X0)
      | m1_pre_topc(X0,sK1) ) ),
    inference(superposition,[],[f46,f33])).

fof(f93,plain,(
    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(subsumption_resolution,[],[f91,f36])).

fof(f91,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f67,f47])).

fof(f67,plain,(
    m1_pre_topc(sK0,sK0) ),
    inference(resolution,[],[f36,f52])).

fof(f65,plain,(
    m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f63,f35])).

fof(f35,plain,(
    ~ v3_tdlat_3(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f63,plain,
    ( m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | v3_tdlat_3(sK1) ),
    inference(resolution,[],[f32,f38])).

fof(f38,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
            | ~ r2_hidden(X1,u1_pre_topc(X0))
            | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) ) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v3_tdlat_3(X0)
      <=> ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( r2_hidden(X1,u1_pre_topc(X0))
             => r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tdlat_3)).

fof(f203,plain,
    ( ~ m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))
    | ~ v3_tdlat_3(sK0) ),
    inference(resolution,[],[f200,f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))
      | ~ v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f200,plain,(
    r2_hidden(sK2(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f199,f36])).

fof(f199,plain,
    ( r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f198,f164])).

fof(f198,plain,
    ( ~ m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | r2_hidden(sK2(sK1),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f197,f55])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f197,plain,(
    v3_pre_topc(sK2(sK1),sK0) ),
    inference(subsumption_resolution,[],[f196,f164])).

fof(f196,plain,
    ( ~ m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2(sK1),sK0) ),
    inference(resolution,[],[f150,f99])).

fof(f99,plain,(
    v3_pre_topc(sK2(sK1),sK1) ),
    inference(subsumption_resolution,[],[f98,f32])).

fof(f98,plain,
    ( ~ l1_pre_topc(sK1)
    | v3_pre_topc(sK2(sK1),sK1) ),
    inference(subsumption_resolution,[],[f95,f65])).

fof(f95,plain,
    ( ~ m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1)
    | v3_pre_topc(sK2(sK1),sK1) ),
    inference(resolution,[],[f66,f54])).

fof(f54,plain,(
    ! [X0,X1] :
      ( ~ r2_hidden(X1,u1_pre_topc(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f66,plain,(
    r2_hidden(sK2(sK1),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f64,f35])).

fof(f64,plain,
    ( r2_hidden(sK2(sK1),u1_pre_topc(sK1))
    | v3_tdlat_3(sK1) ),
    inference(resolution,[],[f32,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | r2_hidden(sK2(X0),u1_pre_topc(X0))
      | v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f150,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f149,f145])).

fof(f145,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(subsumption_resolution,[],[f141,f32])).

fof(f141,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) ) ),
    inference(resolution,[],[f136,f49])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
             => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).

fof(f149,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f143,f32])).

fof(f143,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | ~ l1_pre_topc(sK1)
      | ~ v3_pre_topc(X1,sK1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X1,sK0) ) ),
    inference(resolution,[],[f136,f60])).

fof(f60,plain,(
    ! [X2,X0,X3] :
      ( ~ m1_pre_topc(X2,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v3_pre_topc(X3,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | v3_pre_topc(X3,X2) ) ),
    inference(equality_resolution,[],[f44])).

fof(f44,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_pre_topc(X2,X0)
      | ~ v3_pre_topc(X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))
      | X1 != X3
      | v3_pre_topc(X3,X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
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
    inference(flattening,[],[f20])).

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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f230,plain,(
    ~ m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(forward_demodulation,[],[f229,f161])).

fof(f229,plain,(
    ~ m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK1))) ),
    inference(subsumption_resolution,[],[f228,f32])).

fof(f228,plain,
    ( ~ m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))
    | ~ l1_pre_topc(sK1) ),
    inference(subsumption_resolution,[],[f227,f186])).

fof(f186,plain,(
    ~ r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1)) ),
    inference(subsumption_resolution,[],[f185,f35])).

fof(f185,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1))
    | v3_tdlat_3(sK1) ),
    inference(subsumption_resolution,[],[f180,f32])).

fof(f180,plain,
    ( ~ r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1)
    | v3_tdlat_3(sK1) ),
    inference(superposition,[],[f40,f161])).

fof(f40,plain,(
    ! [X0] :
      ( ~ r2_hidden(k6_subset_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v3_tdlat_3(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f227,plain,
    ( ~ m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))
    | r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1))
    | ~ l1_pre_topc(sK1) ),
    inference(resolution,[],[f223,f55])).

fof(f223,plain,(
    v3_pre_topc(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),sK1) ),
    inference(subsumption_resolution,[],[f221,f216])).

fof(f221,plain,
    ( ~ m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),sK1) ),
    inference(resolution,[],[f217,f172])).

fof(f172,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | v3_pre_topc(X1,sK1) ) ),
    inference(backward_demodulation,[],[f125,f161])).

fof(f125,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | v3_pre_topc(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f124,f123])).

fof(f123,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f119,f36])).

fof(f119,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))
      | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    inference(resolution,[],[f114,f49])).

fof(f124,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | v3_pre_topc(X1,sK1) ) ),
    inference(subsumption_resolution,[],[f121,f36])).

fof(f121,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1)))
      | v3_pre_topc(X1,sK1) ) ),
    inference(resolution,[],[f114,f60])).

fof(f217,plain,(
    v3_pre_topc(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),sK0) ),
    inference(resolution,[],[f216,f211])).

fof(f211,plain,
    ( ~ m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),sK0) ),
    inference(subsumption_resolution,[],[f208,f36])).

fof(f208,plain,
    ( ~ m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ l1_pre_topc(sK0)
    | v3_pre_topc(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),sK0) ),
    inference(resolution,[],[f207,f54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n019.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 19:11:22 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.50  % (27612)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.22/0.51  % (27609)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.22/0.51  % (27608)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.22/0.51  % (27625)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.22/0.52  % (27610)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.22/0.52  % (27616)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.22/0.52  % (27618)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.22/0.52  % (27619)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.22/0.52  % (27611)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.22/0.53  % (27617)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.22/0.53  % (27607)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.22/0.53  % (27622)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.22/0.53  % (27612)Refutation found. Thanks to Tanya!
% 0.22/0.53  % SZS status Theorem for theBenchmark
% 0.22/0.53  % SZS output start Proof for theBenchmark
% 0.22/0.53  fof(f231,plain,(
% 0.22/0.53    $false),
% 0.22/0.53    inference(subsumption_resolution,[],[f230,f216])).
% 0.22/0.53  fof(f216,plain,(
% 0.22/0.53    m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(resolution,[],[f210,f68])).
% 0.22/0.53  fof(f68,plain,(
% 0.22/0.53    m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.22/0.53    inference(resolution,[],[f36,f48])).
% 0.22/0.53  fof(f48,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0))))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f24])).
% 0.22/0.53  fof(f24,plain,(
% 0.22/0.53    ! [X0] : (m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f6])).
% 0.22/0.53  fof(f6,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => m1_subset_1(u1_pre_topc(X0),k1_zfmisc_1(k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_u1_pre_topc)).
% 0.22/0.53  fof(f36,plain,(
% 0.22/0.53    l1_pre_topc(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f17,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : (~v3_tdlat_3(X1) & v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f16])).
% 0.22/0.53  fof(f16,plain,(
% 0.22/0.53    ? [X0] : (? [X1] : ((~v3_tdlat_3(X1) & (v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) & l1_pre_topc(X1)) & l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f15])).
% 0.22/0.53  fof(f15,negated_conjecture,(
% 0.22/0.53    ~! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tdlat_3(X1))))),
% 0.22/0.53    inference(negated_conjecture,[],[f14])).
% 0.22/0.53  fof(f14,conjecture,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ((v3_tdlat_3(X0) & g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) => v3_tdlat_3(X1))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_tex_2)).
% 0.22/0.53  fof(f210,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_subset_1(u1_pre_topc(sK0),k1_zfmisc_1(X0)) | m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),X0)) )),
% 0.22/0.53    inference(resolution,[],[f207,f53])).
% 0.22/0.53  fof(f53,plain,(
% 0.22/0.53    ( ! [X2,X0,X1] : (~r2_hidden(X0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | m1_subset_1(X0,X2)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f30])).
% 0.22/0.53  fof(f30,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | ~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1))),
% 0.22/0.53    inference(flattening,[],[f29])).
% 0.22/0.53  fof(f29,plain,(
% 0.22/0.53    ! [X0,X1,X2] : (m1_subset_1(X0,X2) | (~m1_subset_1(X1,k1_zfmisc_1(X2)) | ~r2_hidden(X0,X1)))),
% 0.22/0.53    inference(ennf_transformation,[],[f3])).
% 0.22/0.53  fof(f3,axiom,(
% 0.22/0.53    ! [X0,X1,X2] : ((m1_subset_1(X1,k1_zfmisc_1(X2)) & r2_hidden(X0,X1)) => m1_subset_1(X0,X2))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_subset)).
% 0.22/0.53  fof(f207,plain,(
% 0.22/0.53    r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0))),
% 0.22/0.53    inference(subsumption_resolution,[],[f206,f34])).
% 0.22/0.53  fof(f34,plain,(
% 0.22/0.53    v3_tdlat_3(sK0)),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f206,plain,(
% 0.22/0.53    r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) | ~v3_tdlat_3(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f205,f36])).
% 0.22/0.53  fof(f205,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) | ~v3_tdlat_3(sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f203,f164])).
% 0.22/0.53  fof(f164,plain,(
% 0.22/0.53    m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(backward_demodulation,[],[f65,f161])).
% 0.22/0.53  fof(f161,plain,(
% 0.22/0.53    u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.22/0.53    inference(subsumption_resolution,[],[f160,f151])).
% 0.22/0.53  fof(f151,plain,(
% 0.22/0.53    r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.22/0.53    inference(resolution,[],[f122,f57])).
% 0.22/0.53  fof(f57,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(X1)) | r1_tarski(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f2])).
% 0.22/0.53  fof(f2,axiom,(
% 0.22/0.53    ! [X0,X1] : (m1_subset_1(X0,k1_zfmisc_1(X1)) <=> r1_tarski(X0,X1))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_subset)).
% 0.22/0.53  fof(f122,plain,(
% 0.22/0.53    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(subsumption_resolution,[],[f118,f36])).
% 0.22/0.53  fof(f118,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.22/0.53    inference(resolution,[],[f114,f50])).
% 0.22/0.53  fof(f50,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.22/0.53    inference(cnf_transformation,[],[f26])).
% 0.22/0.53  fof(f26,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f11])).
% 0.22/0.53  fof(f11,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.22/0.53  fof(f114,plain,(
% 0.22/0.53    m1_pre_topc(sK1,sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f113,f32])).
% 0.22/0.53  fof(f32,plain,(
% 0.22/0.53    l1_pre_topc(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f113,plain,(
% 0.22/0.53    ~l1_pre_topc(sK1) | m1_pre_topc(sK1,sK0)),
% 0.22/0.53    inference(subsumption_resolution,[],[f106,f36])).
% 0.22/0.53  fof(f106,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | ~l1_pre_topc(sK1) | m1_pre_topc(sK1,sK0)),
% 0.22/0.53    inference(resolution,[],[f80,f46])).
% 0.22/0.53  fof(f46,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | m1_pre_topc(X0,X1)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f23,plain,(
% 0.22/0.53    ! [X0] : (! [X1] : ((m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1)))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f9])).
% 0.22/0.53  fof(f9,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => (m1_pre_topc(X0,X1) <=> m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_pre_topc)).
% 0.22/0.53  fof(f80,plain,(
% 0.22/0.53    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.53    inference(forward_demodulation,[],[f79,f33])).
% 0.22/0.53  fof(f33,plain,(
% 0.22/0.53    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f79,plain,(
% 0.22/0.53    m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.22/0.53    inference(subsumption_resolution,[],[f77,f32])).
% 0.22/0.53  fof(f77,plain,(
% 0.22/0.53    ~l1_pre_topc(sK1) | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1)))),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f74])).
% 0.22/0.53  fof(f74,plain,(
% 0.22/0.53    ~l1_pre_topc(sK1) | m1_pre_topc(sK1,g1_pre_topc(u1_struct_0(sK1),u1_pre_topc(sK1))) | ~l1_pre_topc(sK1)),
% 0.22/0.53    inference(resolution,[],[f61,f47])).
% 0.22/0.53  fof(f47,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~m1_pre_topc(X0,X1) | ~l1_pre_topc(X1) | m1_pre_topc(X0,g1_pre_topc(u1_struct_0(X1),u1_pre_topc(X1))) | ~l1_pre_topc(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f23])).
% 0.22/0.53  fof(f61,plain,(
% 0.22/0.53    m1_pre_topc(sK1,sK1)),
% 0.22/0.53    inference(resolution,[],[f32,f52])).
% 0.22/0.53  fof(f52,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_pre_topc(X0) | m1_pre_topc(X0,X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f28])).
% 0.22/0.53  fof(f28,plain,(
% 0.22/0.53    ! [X0] : (m1_pre_topc(X0,X0) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f12])).
% 0.22/0.53  fof(f12,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => m1_pre_topc(X0,X0))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_tsep_1)).
% 0.22/0.53  fof(f160,plain,(
% 0.22/0.53    ~r1_tarski(u1_struct_0(sK1),u1_struct_0(sK0)) | u1_struct_0(sK0) = u1_struct_0(sK1)),
% 0.22/0.53    inference(resolution,[],[f156,f43])).
% 0.22/0.53  fof(f43,plain,(
% 0.22/0.53    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 0.22/0.53    inference(cnf_transformation,[],[f1])).
% 0.22/0.53  fof(f1,axiom,(
% 0.22/0.53    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.22/0.53  fof(f156,plain,(
% 0.22/0.53    r1_tarski(u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.22/0.53    inference(resolution,[],[f144,f57])).
% 0.22/0.53  fof(f144,plain,(
% 0.22/0.53    m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.53    inference(subsumption_resolution,[],[f140,f32])).
% 0.22/0.53  fof(f140,plain,(
% 0.22/0.53    ~l1_pre_topc(sK1) | m1_subset_1(u1_struct_0(sK0),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.53    inference(resolution,[],[f136,f50])).
% 0.22/0.53  fof(f136,plain,(
% 0.22/0.53    m1_pre_topc(sK0,sK1)),
% 0.22/0.53    inference(subsumption_resolution,[],[f126,f36])).
% 0.22/0.53  fof(f126,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | m1_pre_topc(sK0,sK1)),
% 0.22/0.53    inference(resolution,[],[f93,f83])).
% 0.22/0.53  fof(f83,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(X0) | m1_pre_topc(X0,sK1)) )),
% 0.22/0.53    inference(subsumption_resolution,[],[f81,f32])).
% 0.22/0.53  fof(f81,plain,(
% 0.22/0.53    ( ! [X0] : (~m1_pre_topc(X0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK1) | ~l1_pre_topc(X0) | m1_pre_topc(X0,sK1)) )),
% 0.22/0.53    inference(superposition,[],[f46,f33])).
% 0.22/0.53  fof(f93,plain,(
% 0.22/0.53    m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.53    inference(subsumption_resolution,[],[f91,f36])).
% 0.22/0.53  fof(f91,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)))),
% 0.22/0.53    inference(duplicate_literal_removal,[],[f88])).
% 0.22/0.53  fof(f88,plain,(
% 0.22/0.53    ~l1_pre_topc(sK0) | m1_pre_topc(sK0,g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(sK0)),
% 0.22/0.53    inference(resolution,[],[f67,f47])).
% 0.22/0.53  fof(f67,plain,(
% 0.22/0.53    m1_pre_topc(sK0,sK0)),
% 0.22/0.53    inference(resolution,[],[f36,f52])).
% 0.22/0.53  fof(f65,plain,(
% 0.22/0.53    m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK1)))),
% 0.22/0.53    inference(subsumption_resolution,[],[f63,f35])).
% 0.22/0.53  fof(f35,plain,(
% 0.22/0.53    ~v3_tdlat_3(sK1)),
% 0.22/0.53    inference(cnf_transformation,[],[f17])).
% 0.22/0.53  fof(f63,plain,(
% 0.22/0.53    m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | v3_tdlat_3(sK1)),
% 0.22/0.53    inference(resolution,[],[f32,f38])).
% 0.22/0.53  fof(f38,plain,(
% 0.22/0.53    ( ! [X0] : (~l1_pre_topc(X0) | m1_subset_1(sK2(X0),k1_zfmisc_1(u1_struct_0(X0))) | v3_tdlat_3(X0)) )),
% 0.22/0.53    inference(cnf_transformation,[],[f19])).
% 0.22/0.53  fof(f19,plain,(
% 0.22/0.53    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : (r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(flattening,[],[f18])).
% 0.22/0.53  fof(f18,plain,(
% 0.22/0.53    ! [X0] : ((v3_tdlat_3(X0) <=> ! [X1] : ((r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))))) | ~l1_pre_topc(X0))),
% 0.22/0.53    inference(ennf_transformation,[],[f13])).
% 0.22/0.53  fof(f13,axiom,(
% 0.22/0.53    ! [X0] : (l1_pre_topc(X0) => (v3_tdlat_3(X0) <=> ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) => r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0))))))),
% 0.22/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tdlat_3)).
% 0.22/0.53  fof(f203,plain,(
% 0.22/0.53    ~m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK0)) | ~v3_tdlat_3(sK0)),
% 1.33/0.53    inference(resolution,[],[f200,f37])).
% 1.33/0.53  fof(f37,plain,(
% 1.33/0.53    ( ! [X0,X1] : (~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r2_hidden(k6_subset_1(u1_struct_0(X0),X1),u1_pre_topc(X0)) | ~v3_tdlat_3(X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f19])).
% 1.33/0.53  fof(f200,plain,(
% 1.33/0.53    r2_hidden(sK2(sK1),u1_pre_topc(sK0))),
% 1.33/0.53    inference(subsumption_resolution,[],[f199,f36])).
% 1.33/0.53  fof(f199,plain,(
% 1.33/0.53    r2_hidden(sK2(sK1),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 1.33/0.53    inference(subsumption_resolution,[],[f198,f164])).
% 1.33/0.53  fof(f198,plain,(
% 1.33/0.53    ~m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | r2_hidden(sK2(sK1),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 1.33/0.53    inference(resolution,[],[f197,f55])).
% 1.33/0.53  fof(f55,plain,(
% 1.33/0.53    ( ! [X0,X1] : (~v3_pre_topc(X1,X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f31])).
% 1.33/0.53  fof(f31,plain,(
% 1.33/0.53    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.53    inference(ennf_transformation,[],[f4])).
% 1.33/0.53  fof(f4,axiom,(
% 1.33/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 1.33/0.53  fof(f197,plain,(
% 1.33/0.53    v3_pre_topc(sK2(sK1),sK0)),
% 1.33/0.53    inference(subsumption_resolution,[],[f196,f164])).
% 1.33/0.53  fof(f196,plain,(
% 1.33/0.53    ~m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK2(sK1),sK0)),
% 1.33/0.53    inference(resolution,[],[f150,f99])).
% 1.33/0.53  fof(f99,plain,(
% 1.33/0.53    v3_pre_topc(sK2(sK1),sK1)),
% 1.33/0.53    inference(subsumption_resolution,[],[f98,f32])).
% 1.33/0.53  fof(f98,plain,(
% 1.33/0.53    ~l1_pre_topc(sK1) | v3_pre_topc(sK2(sK1),sK1)),
% 1.33/0.53    inference(subsumption_resolution,[],[f95,f65])).
% 1.33/0.53  fof(f95,plain,(
% 1.33/0.53    ~m1_subset_1(sK2(sK1),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | v3_pre_topc(sK2(sK1),sK1)),
% 1.33/0.53    inference(resolution,[],[f66,f54])).
% 1.33/0.53  fof(f54,plain,(
% 1.33/0.53    ( ! [X0,X1] : (~r2_hidden(X1,u1_pre_topc(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v3_pre_topc(X1,X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f31])).
% 1.33/0.53  fof(f66,plain,(
% 1.33/0.53    r2_hidden(sK2(sK1),u1_pre_topc(sK1))),
% 1.33/0.53    inference(subsumption_resolution,[],[f64,f35])).
% 1.33/0.53  fof(f64,plain,(
% 1.33/0.53    r2_hidden(sK2(sK1),u1_pre_topc(sK1)) | v3_tdlat_3(sK1)),
% 1.33/0.53    inference(resolution,[],[f32,f39])).
% 1.33/0.53  fof(f39,plain,(
% 1.33/0.53    ( ! [X0] : (~l1_pre_topc(X0) | r2_hidden(sK2(X0),u1_pre_topc(X0)) | v3_tdlat_3(X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f19])).
% 1.33/0.53  fof(f150,plain,(
% 1.33/0.53    ( ! [X1] : (~v3_pre_topc(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X1,sK0)) )),
% 1.33/0.53    inference(subsumption_resolution,[],[f149,f145])).
% 1.33/0.53  fof(f145,plain,(
% 1.33/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 1.33/0.53    inference(subsumption_resolution,[],[f141,f32])).
% 1.33/0.53  fof(f141,plain,(
% 1.33/0.53    ( ! [X0] : (~l1_pre_topc(sK1) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1)))) )),
% 1.33/0.53    inference(resolution,[],[f136,f49])).
% 1.33/0.53  fof(f49,plain,(
% 1.33/0.53    ( ! [X2,X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) )),
% 1.33/0.53    inference(cnf_transformation,[],[f25])).
% 1.33/0.53  fof(f25,plain,(
% 1.33/0.53    ! [X0] : (! [X1] : (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 1.33/0.53    inference(ennf_transformation,[],[f7])).
% 1.33/0.53  fof(f7,axiom,(
% 1.33/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) => m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_pre_topc)).
% 1.33/0.53  fof(f149,plain,(
% 1.33/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~v3_pre_topc(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X1,sK0)) )),
% 1.33/0.53    inference(subsumption_resolution,[],[f143,f32])).
% 1.33/0.53  fof(f143,plain,(
% 1.33/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1) | ~v3_pre_topc(X1,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X1,sK0)) )),
% 1.33/0.53    inference(resolution,[],[f136,f60])).
% 1.33/0.53  fof(f60,plain,(
% 1.33/0.53    ( ! [X2,X0,X3] : (~m1_pre_topc(X2,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v3_pre_topc(X3,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | v3_pre_topc(X3,X2)) )),
% 1.33/0.53    inference(equality_resolution,[],[f44])).
% 1.33/0.53  fof(f44,plain,(
% 1.33/0.53    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X2,X0) | ~v3_pre_topc(X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) | X1 != X3 | v3_pre_topc(X3,X2)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f21])).
% 1.33/0.53  fof(f21,plain,(
% 1.33/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (v3_pre_topc(X3,X2) | X1 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.53    inference(flattening,[],[f20])).
% 1.33/0.53  fof(f20,plain,(
% 1.33/0.53    ! [X0] : (! [X1] : (! [X2] : ((! [X3] : ((v3_pre_topc(X3,X2) | X1 != X3) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2)))) | ~v3_pre_topc(X1,X0)) | ~m1_pre_topc(X2,X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.33/0.53    inference(ennf_transformation,[],[f10])).
% 1.33/0.53  fof(f10,axiom,(
% 1.33/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_pre_topc(X2,X0) => (v3_pre_topc(X1,X0) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X2))) => (X1 = X3 => v3_pre_topc(X3,X2)))))))),
% 1.33/0.53    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t33_tops_2)).
% 1.33/0.53  fof(f230,plain,(
% 1.33/0.53    ~m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.33/0.53    inference(forward_demodulation,[],[f229,f161])).
% 1.33/0.53  fof(f229,plain,(
% 1.33/0.53    ~m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK1)))),
% 1.33/0.53    inference(subsumption_resolution,[],[f228,f32])).
% 1.33/0.53  fof(f228,plain,(
% 1.33/0.53    ~m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK1))) | ~l1_pre_topc(sK1)),
% 1.33/0.53    inference(subsumption_resolution,[],[f227,f186])).
% 1.33/0.53  fof(f186,plain,(
% 1.33/0.53    ~r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1))),
% 1.33/0.53    inference(subsumption_resolution,[],[f185,f35])).
% 1.33/0.53  fof(f185,plain,(
% 1.33/0.53    ~r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1)) | v3_tdlat_3(sK1)),
% 1.33/0.53    inference(subsumption_resolution,[],[f180,f32])).
% 1.33/0.53  fof(f180,plain,(
% 1.33/0.53    ~r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1)) | ~l1_pre_topc(sK1) | v3_tdlat_3(sK1)),
% 1.33/0.53    inference(superposition,[],[f40,f161])).
% 1.33/0.53  fof(f40,plain,(
% 1.33/0.53    ( ! [X0] : (~r2_hidden(k6_subset_1(u1_struct_0(X0),sK2(X0)),u1_pre_topc(X0)) | ~l1_pre_topc(X0) | v3_tdlat_3(X0)) )),
% 1.33/0.53    inference(cnf_transformation,[],[f19])).
% 1.33/0.53  fof(f227,plain,(
% 1.33/0.53    ~m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK1))) | r2_hidden(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),u1_pre_topc(sK1)) | ~l1_pre_topc(sK1)),
% 1.33/0.53    inference(resolution,[],[f223,f55])).
% 1.33/0.53  fof(f223,plain,(
% 1.33/0.53    v3_pre_topc(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),sK1)),
% 1.33/0.53    inference(subsumption_resolution,[],[f221,f216])).
% 1.33/0.53  fof(f221,plain,(
% 1.33/0.53    ~m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),sK1)),
% 1.33/0.53    inference(resolution,[],[f217,f172])).
% 1.33/0.53  fof(f172,plain,(
% 1.33/0.53    ( ! [X1] : (~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(X1,sK1)) )),
% 1.33/0.53    inference(backward_demodulation,[],[f125,f161])).
% 1.33/0.53  fof(f125,plain,(
% 1.33/0.53    ( ! [X1] : (~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(X1,sK1)) )),
% 1.33/0.53    inference(subsumption_resolution,[],[f124,f123])).
% 1.33/0.53  fof(f123,plain,(
% 1.33/0.53    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.33/0.53    inference(subsumption_resolution,[],[f119,f36])).
% 1.33/0.53  fof(f119,plain,(
% 1.33/0.53    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK1))) | m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))) )),
% 1.33/0.53    inference(resolution,[],[f114,f49])).
% 1.33/0.53  fof(f124,plain,(
% 1.33/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(X1,sK1)) )),
% 1.33/0.53    inference(subsumption_resolution,[],[f121,f36])).
% 1.33/0.53  fof(f121,plain,(
% 1.33/0.53    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK1))) | v3_pre_topc(X1,sK1)) )),
% 1.33/0.53    inference(resolution,[],[f114,f60])).
% 1.33/0.53  fof(f217,plain,(
% 1.33/0.53    v3_pre_topc(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),sK0)),
% 1.33/0.53    inference(resolution,[],[f216,f211])).
% 1.33/0.53  fof(f211,plain,(
% 1.33/0.53    ~m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),sK0)),
% 1.33/0.53    inference(subsumption_resolution,[],[f208,f36])).
% 1.33/0.53  fof(f208,plain,(
% 1.33/0.53    ~m1_subset_1(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0) | v3_pre_topc(k6_subset_1(u1_struct_0(sK0),sK2(sK1)),sK0)),
% 1.33/0.53    inference(resolution,[],[f207,f54])).
% 1.33/0.53  % SZS output end Proof for theBenchmark
% 1.33/0.53  % (27612)------------------------------
% 1.33/0.53  % (27612)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (27612)Termination reason: Refutation
% 1.33/0.53  
% 1.33/0.53  % (27612)Memory used [KB]: 6140
% 1.33/0.53  % (27612)Time elapsed: 0.107 s
% 1.33/0.53  % (27612)------------------------------
% 1.33/0.53  % (27612)------------------------------
% 1.33/0.53  % (27607)Refutation not found, incomplete strategy% (27607)------------------------------
% 1.33/0.53  % (27607)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.33/0.53  % (27607)Termination reason: Refutation not found, incomplete strategy
% 1.33/0.53  
% 1.33/0.53  % (27607)Memory used [KB]: 10618
% 1.33/0.53  % (27607)Time elapsed: 0.099 s
% 1.33/0.53  % (27607)------------------------------
% 1.33/0.53  % (27607)------------------------------
% 1.33/0.53  % (27606)Success in time 0.166 s
%------------------------------------------------------------------------------
