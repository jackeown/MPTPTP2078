%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:33 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  173 (1768 expanded)
%              Number of leaves         :   15 ( 345 expanded)
%              Depth                    :   26
%              Number of atoms          :  556 (8868 expanded)
%              Number of equality atoms :  117 (1274 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f726,plain,(
    $false ),
    inference(subsumption_resolution,[],[f725,f719])).

fof(f719,plain,(
    k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f294,f717])).

fof(f717,plain,(
    v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f663,f716])).

fof(f716,plain,(
    v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f142,f704])).

fof(f704,plain,(
    r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f154,f703])).

fof(f703,plain,(
    u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f688])).

fof(f688,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))
    | u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(superposition,[],[f288,f483])).

fof(f483,plain,
    ( k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK0))
    | u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f379,f158])).

fof(f158,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f157,f124])).

fof(f124,plain,(
    u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f123,f44])).

fof(f44,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) )
          & m1_pre_topc(X1,X0)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( ( m1_pre_topc(X1,X0)
              & ~ v2_struct_0(X1) )
           => ( ( m1_pre_topc(X1,X0)
                & v1_tsep_1(X1,X0) )
            <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ( m1_pre_topc(X1,X0)
              & v1_tsep_1(X1,X0) )
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_tmap_1)).

fof(f123,plain,
    ( v2_struct_0(sK0)
    | u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f122,f42])).

fof(f42,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f122,plain,
    ( v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f121,f46])).

fof(f46,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f121,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(subsumption_resolution,[],[f120,f45])).

fof(f45,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f120,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1)) ),
    inference(resolution,[],[f77,f43])).

fof(f43,plain,(
    m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f77,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(subsumption_resolution,[],[f73,f52])).

fof(f52,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1)) ) ),
    inference(equality_resolution,[],[f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( ! [X2] :
                ( u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) )
          | ~ m1_pre_topc(X1,X0)
          | v2_struct_0(X1) )
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
          ( ( m1_pre_topc(X1,X0)
            & ~ v2_struct_0(X1) )
         => ( ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) ) )
            & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_tmap_1)).

fof(f157,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f156,f44])).

fof(f156,plain,
    ( v2_struct_0(sK0)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f155,f46])).

fof(f155,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f138,f45])).

fof(f138,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1))
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f85,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ r2_hidden(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f85,plain,(
    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f84,f46])).

fof(f84,plain,
    ( ~ l1_pre_topc(sK0)
    | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(resolution,[],[f52,f43])).

fof(f379,plain,
    ( r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK0)) ),
    inference(resolution,[],[f143,f293])).

fof(f293,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f88,f292])).

fof(f292,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f291,f256])).

fof(f256,plain,(
    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f255,f44])).

fof(f255,plain,
    ( v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f253,f46])).

fof(f253,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    inference(resolution,[],[f112,f45])).

fof(f112,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0))) ) ),
    inference(resolution,[],[f59,f75])).

fof(f75,plain,(
    ! [X0] : m1_subset_1(X0,k1_zfmisc_1(X0)) ),
    inference(forward_demodulation,[],[f48,f47])).

fof(f47,plain,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] : k2_subset_1(X0) = X0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).

fof(f48,plain,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).

fof(f59,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f291,plain,(
    k6_tmap_1(sK0,u1_struct_0(sK0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f290,f288])).

fof(f290,plain,(
    k6_tmap_1(sK0,u1_struct_0(sK0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f289,f250])).

fof(f250,plain,(
    l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f249,f44])).

fof(f249,plain,
    ( v2_struct_0(sK0)
    | l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f247,f46])).

fof(f247,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    inference(resolution,[],[f109,f45])).

fof(f109,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | l1_pre_topc(k6_tmap_1(X0,u1_struct_0(X0))) ) ),
    inference(resolution,[],[f71,f75])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | l1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f289,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))
    | k6_tmap_1(sK0,u1_struct_0(sK0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))) ),
    inference(resolution,[],[f238,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0
      | ~ v1_pre_topc(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ( v1_pre_topc(X0)
       => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).

fof(f238,plain,(
    v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f237,f44])).

fof(f237,plain,
    ( v2_struct_0(sK0)
    | v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f235,f46])).

fof(f235,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    inference(resolution,[],[f107,f45])).

fof(f107,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_pre_topc(k6_tmap_1(X0,u1_struct_0(X0))) ) ),
    inference(resolution,[],[f69,f75])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f88,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f87,f46])).

fof(f87,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f86,f43])).

fof(f86,plain,
    ( ~ m1_pre_topc(sK1,sK0)
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f76,f40])).

fof(f40,plain,
    ( v1_tsep_1(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) ),
    inference(cnf_transformation,[],[f18])).

fof(f76,plain,(
    ! [X0,X1] :
      ( ~ v1_tsep_1(X1,X0)
      | ~ m1_pre_topc(X1,X0)
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(subsumption_resolution,[],[f72,f52])).

fof(f72,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(u1_struct_0(X1),X0)
      | ~ v1_tsep_1(X1,X0) ) ),
    inference(equality_resolution,[],[f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X1) != X2
      | v3_pre_topc(X2,X0)
      | ~ v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( v3_pre_topc(X2,X0)
                | u1_struct_0(X1) != X2
                | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) ) )
          | ~ m1_pre_topc(X1,X0) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_pre_topc(X1,X0)
         => ( v1_tsep_1(X1,X0)
          <=> ! [X2] :
                ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
               => ( u1_struct_0(X1) = X2
                 => v3_pre_topc(X2,X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tsep_1)).

fof(f143,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f134,f46])).

fof(f134,plain,
    ( ~ l1_pre_topc(sK0)
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | ~ v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(resolution,[],[f85,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> r2_hidden(X1,u1_pre_topc(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f288,plain,(
    u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f262,f287])).

fof(f287,plain,(
    u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f286,f45])).

fof(f286,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f285,f44])).

fof(f285,plain,
    ( v2_struct_0(sK0)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f283,f46])).

fof(f283,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0))
    | ~ v2_pre_topc(sK0) ),
    inference(resolution,[],[f232,f126])).

fof(f126,plain,(
    ! [X0] :
      ( ~ r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | u1_pre_topc(X0) = k5_tmap_1(X0,u1_struct_0(X0))
      | ~ v2_pre_topc(X0) ) ),
    inference(resolution,[],[f62,f75])).

fof(f232,plain,(
    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f230,f46])).

fof(f230,plain,
    ( r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f104,f82])).

fof(f82,plain,(
    v3_pre_topc(u1_struct_0(sK0),sK0) ),
    inference(backward_demodulation,[],[f80,f81])).

fof(f81,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f78,f49])).

fof(f49,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | u1_struct_0(X0) = k2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( u1_struct_0(X0) = k2_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => u1_struct_0(X0) = k2_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f78,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f50,f46])).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f80,plain,(
    v3_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(subsumption_resolution,[],[f79,f46])).

fof(f79,plain,
    ( ~ l1_pre_topc(sK0)
    | v3_pre_topc(k2_struct_0(sK0),sK0) ),
    inference(resolution,[],[f65,f45])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v3_pre_topc(k2_struct_0(X0),X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v3_pre_topc(k2_struct_0(X0),X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => v3_pre_topc(k2_struct_0(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).

fof(f104,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(u1_struct_0(X0),X0)
      | r2_hidden(u1_struct_0(X0),u1_pre_topc(X0))
      | ~ l1_pre_topc(X0) ) ),
    inference(resolution,[],[f58,f75])).

fof(f262,plain,(
    k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f261,f44])).

fof(f261,plain,
    ( v2_struct_0(sK0)
    | k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f259,f46])).

fof(f259,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) ),
    inference(resolution,[],[f119,f45])).

fof(f119,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | k5_tmap_1(X0,u1_struct_0(X0)) = u1_pre_topc(k6_tmap_1(X0,u1_struct_0(X0))) ) ),
    inference(resolution,[],[f60,f75])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f154,plain,
    ( u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1))
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f153,f124])).

fof(f153,plain,
    ( u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK1))
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f152,f44])).

fof(f152,plain,
    ( v2_struct_0(sK0)
    | u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK1))
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f151,f46])).

fof(f151,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK1))
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f137,f45])).

fof(f137,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK1))
    | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f85,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | u1_pre_topc(X0) != k5_tmap_1(X0,X1)
      | r2_hidden(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f142,plain,
    ( ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(subsumption_resolution,[],[f133,f46])).

fof(f133,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | v3_pre_topc(u1_struct_0(sK1),sK0) ),
    inference(resolution,[],[f85,f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f663,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f662,f46])).

fof(f662,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0)
    | v1_tsep_1(sK1,sK0) ),
    inference(subsumption_resolution,[],[f661,f43])).

fof(f661,plain,
    ( ~ v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ m1_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | v1_tsep_1(sK1,sK0) ),
    inference(superposition,[],[f56,f531])).

fof(f531,plain,(
    u1_struct_0(sK1) = sK2(sK0,sK1) ),
    inference(subsumption_resolution,[],[f526,f193])).

fof(f193,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
    | u1_struct_0(sK1) = sK2(sK0,sK1) ),
    inference(resolution,[],[f102,f74])).

fof(f74,plain,
    ( ~ v1_tsep_1(sK1,sK0)
    | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f39,f43])).

fof(f39,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)
    | ~ v1_tsep_1(sK1,sK0)
    | ~ m1_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f102,plain,
    ( v1_tsep_1(sK1,sK0)
    | u1_struct_0(sK1) = sK2(sK0,sK1) ),
    inference(subsumption_resolution,[],[f101,f46])).

fof(f101,plain,
    ( ~ l1_pre_topc(sK0)
    | u1_struct_0(sK1) = sK2(sK0,sK1)
    | v1_tsep_1(sK1,sK0) ),
    inference(resolution,[],[f55,f43])).

fof(f55,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | u1_struct_0(X1) = sK2(X0,X1)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f526,plain,
    ( g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)
    | u1_struct_0(sK1) = sK2(sK0,sK1) ),
    inference(superposition,[],[f118,f446])).

fof(f446,plain,
    ( u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))
    | u1_struct_0(sK1) = sK2(sK0,sK1) ),
    inference(resolution,[],[f397,f158])).

fof(f397,plain,
    ( r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))
    | u1_struct_0(sK1) = sK2(sK0,sK1) ),
    inference(resolution,[],[f196,f143])).

fof(f196,plain,
    ( v3_pre_topc(u1_struct_0(sK1),sK0)
    | u1_struct_0(sK1) = sK2(sK0,sK1) ),
    inference(subsumption_resolution,[],[f195,f46])).

fof(f195,plain,
    ( u1_struct_0(sK1) = sK2(sK0,sK1)
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(subsumption_resolution,[],[f194,f43])).

fof(f194,plain,
    ( u1_struct_0(sK1) = sK2(sK0,sK1)
    | ~ m1_pre_topc(sK1,sK0)
    | v3_pre_topc(u1_struct_0(sK1),sK0)
    | ~ l1_pre_topc(sK0) ),
    inference(resolution,[],[f102,f76])).

fof(f118,plain,(
    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1))) ),
    inference(backward_demodulation,[],[f111,f117])).

fof(f117,plain,(
    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f116,f44])).

fof(f116,plain,
    ( v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f115,f42])).

fof(f115,plain,
    ( v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f114,f46])).

fof(f114,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f113,f45])).

fof(f113,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | v2_struct_0(sK0)
    | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f64,f43])).

fof(f64,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | v2_struct_0(X0)
      | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f111,plain,(
    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f110,f100])).

fof(f100,plain,(
    l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f99,f44])).

fof(f99,plain,
    ( v2_struct_0(sK0)
    | l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f98,f46])).

fof(f98,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f97,f45])).

fof(f97,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | l1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f68,f43])).

fof(f68,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | l1_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) )
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_pre_topc(X1,X0)
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k8_tmap_1(X0,X1))
        & v2_pre_topc(k8_tmap_1(X0,X1))
        & v1_pre_topc(k8_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).

fof(f110,plain,
    ( ~ l1_pre_topc(k8_tmap_1(sK0,sK1))
    | k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f92,f51])).

fof(f92,plain,(
    v1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f91,f44])).

fof(f91,plain,
    ( v2_struct_0(sK0)
    | v1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f90,f46])).

fof(f90,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f89,f45])).

fof(f89,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | v2_struct_0(sK0)
    | v1_pre_topc(k8_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f66,f43])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ m1_pre_topc(X1,X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_pre_topc(k8_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ~ v3_pre_topc(sK2(X0,X1),X0)
      | ~ m1_pre_topc(X1,X0)
      | ~ l1_pre_topc(X0)
      | v1_tsep_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f294,plain,
    ( ~ v1_tsep_1(sK1,sK0)
    | k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f74,f292])).

fof(f725,plain,(
    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f292,f705])).

fof(f705,plain,(
    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) ),
    inference(backward_demodulation,[],[f118,f703])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 20:04:57 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.45  % (8610)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.46  % (8625)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.46  % (8608)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.47  % (8616)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.47  % (8618)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.47  % (8608)Refutation not found, incomplete strategy% (8608)------------------------------
% 0.21/0.47  % (8608)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (8618)Refutation not found, incomplete strategy% (8618)------------------------------
% 0.21/0.47  % (8618)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (8626)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.48  % (8621)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (8621)Refutation not found, incomplete strategy% (8621)------------------------------
% 0.21/0.48  % (8621)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (8608)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (8608)Memory used [KB]: 6268
% 0.21/0.48  % (8608)Time elapsed: 0.056 s
% 0.21/0.48  % (8608)------------------------------
% 0.21/0.48  % (8608)------------------------------
% 0.21/0.48  % (8621)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (8621)Memory used [KB]: 1791
% 0.21/0.48  % (8621)Time elapsed: 0.068 s
% 0.21/0.48  % (8621)------------------------------
% 0.21/0.48  % (8621)------------------------------
% 0.21/0.48  % (8618)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (8618)Memory used [KB]: 6268
% 0.21/0.48  % (8618)Time elapsed: 0.066 s
% 0.21/0.48  % (8618)------------------------------
% 0.21/0.48  % (8618)------------------------------
% 0.21/0.49  % (8611)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.49  % (8620)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.49  % (8619)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (8620)Refutation not found, incomplete strategy% (8620)------------------------------
% 0.21/0.49  % (8620)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.49  % (8620)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.49  
% 0.21/0.49  % (8620)Memory used [KB]: 6140
% 0.21/0.49  % (8620)Time elapsed: 0.085 s
% 0.21/0.49  % (8620)------------------------------
% 0.21/0.49  % (8620)------------------------------
% 0.21/0.50  % (8615)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.50  % (8609)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  % (8625)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f726,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(subsumption_resolution,[],[f725,f719])).
% 0.21/0.50  fof(f719,plain,(
% 0.21/0.50    k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,u1_struct_0(sK0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f294,f717])).
% 0.21/0.50  fof(f717,plain,(
% 0.21/0.50    v1_tsep_1(sK1,sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f663,f716])).
% 0.21/0.50  fof(f716,plain,(
% 0.21/0.50    v3_pre_topc(u1_struct_0(sK1),sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f142,f704])).
% 0.21/0.50  fof(f704,plain,(
% 0.21/0.50    r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f154,f703])).
% 0.21/0.50  fof(f703,plain,(
% 0.21/0.50    u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.21/0.50    inference(duplicate_literal_removal,[],[f688])).
% 0.21/0.50  fof(f688,plain,(
% 0.21/0.50    u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1)) | u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.21/0.50    inference(superposition,[],[f288,f483])).
% 0.21/0.50  fof(f483,plain,(
% 0.21/0.50    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK0)) | u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.21/0.50    inference(resolution,[],[f379,f158])).
% 0.21/0.50  fof(f158,plain,(
% 0.21/0.50    ~r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.21/0.50    inference(forward_demodulation,[],[f157,f124])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))),
% 0.21/0.50    inference(subsumption_resolution,[],[f123,f44])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ~v2_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <~> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1)) & (m1_pre_topc(X1,X0) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  fof(f16,negated_conjecture,(
% 0.21/0.50    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 0.21/0.50    inference(negated_conjecture,[],[f15])).
% 0.21/0.50  fof(f15,conjecture,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => ((m1_pre_topc(X1,X0) & v1_tsep_1(X1,X0)) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k8_tmap_1(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t116_tmap_1)).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    v2_struct_0(sK0) | u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))),
% 0.21/0.50    inference(subsumption_resolution,[],[f122,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ~v2_struct_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f122,plain,(
% 0.21/0.50    v2_struct_0(sK1) | v2_struct_0(sK0) | u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))),
% 0.21/0.50    inference(subsumption_resolution,[],[f121,f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    l1_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))),
% 0.21/0.50    inference(subsumption_resolution,[],[f120,f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    v2_pre_topc(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | u1_pre_topc(k8_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,u1_struct_0(sK1))),
% 0.21/0.50    inference(resolution,[],[f77,f43])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    m1_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f73,f52])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_tsep_1)).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,u1_struct_0(X1))) )),
% 0.21/0.50    inference(equality_resolution,[],[f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((! [X2] : (u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((! [X2] : ((u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((m1_pre_topc(X1,X0) & ~v2_struct_0(X1)) => (! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => u1_pre_topc(k8_tmap_1(X0,X1)) = k5_tmap_1(X0,X2))) & u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t114_tmap_1)).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1)) | ~r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f156,f44])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    v2_struct_0(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1)) | ~r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f155,f46])).
% 0.21/0.50  fof(f155,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1)) | ~r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f138,f45])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK1)) | ~r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))),
% 0.21/0.50    inference(resolution,[],[f85,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t103_tmap_1)).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f84,f46])).
% 0.21/0.50  fof(f84,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | m1_subset_1(u1_struct_0(sK1),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.50    inference(resolution,[],[f52,f43])).
% 0.21/0.50  fof(f379,plain,(
% 0.21/0.50    r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK0))),
% 0.21/0.50    inference(resolution,[],[f143,f293])).
% 0.21/0.50  fof(f293,plain,(
% 0.21/0.50    v3_pre_topc(u1_struct_0(sK1),sK0) | k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK0))),
% 0.21/0.50    inference(backward_demodulation,[],[f88,f292])).
% 0.21/0.50  fof(f292,plain,(
% 0.21/0.50    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,u1_struct_0(sK0))),
% 0.21/0.50    inference(forward_demodulation,[],[f291,f256])).
% 0.21/0.50  fof(f256,plain,(
% 0.21/0.50    u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f255,f44])).
% 0.21/0.50  fof(f255,plain,(
% 0.21/0.50    v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f253,f46])).
% 0.21/0.50  fof(f253,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 0.21/0.50    inference(resolution,[],[f112,f45])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,u1_struct_0(X0)))) )),
% 0.21/0.50    inference(resolution,[],[f59,f75])).
% 0.21/0.50  fof(f75,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(forward_demodulation,[],[f48,f47])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    ( ! [X0] : (k2_subset_1(X0) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : k2_subset_1(X0) = X0),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_subset_1)).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ( ! [X0] : (m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0] : m1_subset_1(k2_subset_1(X0),k1_zfmisc_1(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_subset_1)).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).
% 0.21/0.50  fof(f291,plain,(
% 0.21/0.50    k6_tmap_1(sK0,u1_struct_0(sK0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),u1_pre_topc(sK0))),
% 0.21/0.50    inference(forward_demodulation,[],[f290,f288])).
% 0.21/0.50  fof(f290,plain,(
% 0.21/0.50    k6_tmap_1(sK0,u1_struct_0(sK0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))))),
% 0.21/0.50    inference(subsumption_resolution,[],[f289,f250])).
% 0.21/0.50  fof(f250,plain,(
% 0.21/0.50    l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f249,f44])).
% 0.21/0.50  fof(f249,plain,(
% 0.21/0.50    v2_struct_0(sK0) | l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f247,f46])).
% 0.21/0.50  fof(f247,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 0.21/0.50    inference(resolution,[],[f109,f45])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | l1_pre_topc(k6_tmap_1(X0,u1_struct_0(X0)))) )),
% 0.21/0.50    inference(resolution,[],[f71,f75])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | l1_pre_topc(k6_tmap_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 0.21/0.50  fof(f289,plain,(
% 0.21/0.50    ~l1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))) | k6_tmap_1(sK0,u1_struct_0(sK0)) = g1_pre_topc(u1_struct_0(k6_tmap_1(sK0,u1_struct_0(sK0))),u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0))))),
% 0.21/0.50    inference(resolution,[],[f238,f51])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_pre_topc(X0) | ~l1_pre_topc(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : ((g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0 | ~v1_pre_topc(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => (v1_pre_topc(X0) => g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',abstractness_v1_pre_topc)).
% 0.21/0.50  fof(f238,plain,(
% 0.21/0.50    v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f237,f44])).
% 0.21/0.50  fof(f237,plain,(
% 0.21/0.50    v2_struct_0(sK0) | v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f235,f46])).
% 0.21/0.50  fof(f235,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 0.21/0.50    inference(resolution,[],[f107,f45])).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_pre_topc(k6_tmap_1(X0,u1_struct_0(X0)))) )),
% 0.21/0.50    inference(resolution,[],[f69,f75])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_pre_topc(k6_tmap_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f38])).
% 0.21/0.50  fof(f88,plain,(
% 0.21/0.50    v3_pre_topc(u1_struct_0(sK1),sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f87,f46])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    v3_pre_topc(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f86,f43])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    ~m1_pre_topc(sK1,sK0) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)),
% 0.21/0.50    inference(resolution,[],[f76,f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    v1_tsep_1(sK1,sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f76,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_tsep_1(X1,X0) | ~m1_pre_topc(X1,X0) | v3_pre_topc(u1_struct_0(X1),X0) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(subsumption_resolution,[],[f72,f52])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(u1_struct_0(X1),k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(u1_struct_0(X1),X0) | ~v1_tsep_1(X1,X0)) )),
% 0.21/0.50    inference(equality_resolution,[],[f53])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~m1_pre_topc(X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X1) != X2 | v3_pre_topc(X2,X0) | ~v1_tsep_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : (v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v1_tsep_1(X1,X0) <=> ! [X2] : ((v3_pre_topc(X2,X0) | u1_struct_0(X1) != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_pre_topc(X1,X0)) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_pre_topc(X1,X0) => (v1_tsep_1(X1,X0) <=> ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) => (u1_struct_0(X1) = X2 => v3_pre_topc(X2,X0))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tsep_1)).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    ~v3_pre_topc(u1_struct_0(sK1),sK0) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f134,f46])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | ~v3_pre_topc(u1_struct_0(sK1),sK0)),
% 0.21/0.50    inference(resolution,[],[f85,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f5])).
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_pre_topc)).
% 0.21/0.50  fof(f288,plain,(
% 0.21/0.50    u1_pre_topc(sK0) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 0.21/0.50    inference(backward_demodulation,[],[f262,f287])).
% 0.21/0.50  fof(f287,plain,(
% 0.21/0.50    u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f286,f45])).
% 0.21/0.50  fof(f286,plain,(
% 0.21/0.50    u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0)) | ~v2_pre_topc(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f285,f44])).
% 0.21/0.50  fof(f285,plain,(
% 0.21/0.50    v2_struct_0(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0)) | ~v2_pre_topc(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f283,f46])).
% 0.21/0.50  fof(f283,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,u1_struct_0(sK0)) | ~v2_pre_topc(sK0)),
% 0.21/0.50    inference(resolution,[],[f232,f126])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    ( ! [X0] : (~r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~l1_pre_topc(X0) | v2_struct_0(X0) | u1_pre_topc(X0) = k5_tmap_1(X0,u1_struct_0(X0)) | ~v2_pre_topc(X0)) )),
% 0.21/0.50    inference(resolution,[],[f62,f75])).
% 0.21/0.50  fof(f232,plain,(
% 0.21/0.50    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f230,f46])).
% 0.21/0.50  fof(f230,plain,(
% 0.21/0.50    r2_hidden(u1_struct_0(sK0),u1_pre_topc(sK0)) | ~l1_pre_topc(sK0)),
% 0.21/0.50    inference(resolution,[],[f104,f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    v3_pre_topc(u1_struct_0(sK0),sK0)),
% 0.21/0.50    inference(backward_demodulation,[],[f80,f81])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f78,f49])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_struct_0(X0) | u1_struct_0(X0) = k2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f19])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ! [X0] : (u1_struct_0(X0) = k2_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) => u1_struct_0(X0) = k2_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    l1_struct_0(sK0)),
% 0.21/0.50    inference(resolution,[],[f50,f46])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 0.21/0.50  fof(f80,plain,(
% 0.21/0.50    v3_pre_topc(k2_struct_0(sK0),sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f79,f46])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | v3_pre_topc(k2_struct_0(sK0),sK0)),
% 0.21/0.50    inference(resolution,[],[f65,f45])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v3_pre_topc(k2_struct_0(X0),X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.50    inference(flattening,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0] : (v3_pre_topc(k2_struct_0(X0),X0) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => v3_pre_topc(k2_struct_0(X0),X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc10_tops_1)).
% 0.21/0.50  fof(f104,plain,(
% 0.21/0.50    ( ! [X0] : (~v3_pre_topc(u1_struct_0(X0),X0) | r2_hidden(u1_struct_0(X0),u1_pre_topc(X0)) | ~l1_pre_topc(X0)) )),
% 0.21/0.50    inference(resolution,[],[f58,f75])).
% 0.21/0.50  fof(f262,plain,(
% 0.21/0.50    k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f261,f44])).
% 0.21/0.50  fof(f261,plain,(
% 0.21/0.50    v2_struct_0(sK0) | k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f259,f46])).
% 0.21/0.50  fof(f259,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | k5_tmap_1(sK0,u1_struct_0(sK0)) = u1_pre_topc(k6_tmap_1(sK0,u1_struct_0(sK0)))),
% 0.21/0.50    inference(resolution,[],[f119,f45])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | k5_tmap_1(X0,u1_struct_0(X0)) = u1_pre_topc(k6_tmap_1(X0,u1_struct_0(X0)))) )),
% 0.21/0.50    inference(resolution,[],[f60,f75])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f28])).
% 0.21/0.50  fof(f154,plain,(
% 0.21/0.50    u1_pre_topc(sK0) != u1_pre_topc(k8_tmap_1(sK0,sK1)) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))),
% 0.21/0.50    inference(forward_demodulation,[],[f153,f124])).
% 0.21/0.50  fof(f153,plain,(
% 0.21/0.50    u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK1)) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f152,f44])).
% 0.21/0.50  fof(f152,plain,(
% 0.21/0.50    v2_struct_0(sK0) | u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK1)) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f151,f46])).
% 0.21/0.50  fof(f151,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK1)) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))),
% 0.21/0.50    inference(subsumption_resolution,[],[f137,f45])).
% 0.21/0.50  fof(f137,plain,(
% 0.21/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | u1_pre_topc(sK0) != k5_tmap_1(sK0,u1_struct_0(sK1)) | r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0))),
% 0.21/0.50    inference(resolution,[],[f85,f61])).
% 0.21/0.50  fof(f61,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | u1_pre_topc(X0) != k5_tmap_1(X0,X1) | r2_hidden(X1,u1_pre_topc(X0))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f30])).
% 0.21/0.50  fof(f142,plain,(
% 0.21/0.50    ~r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | v3_pre_topc(u1_struct_0(sK1),sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f133,f46])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | ~r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | v3_pre_topc(u1_struct_0(sK1),sK0)),
% 0.21/0.50    inference(resolution,[],[f85,f57])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f26])).
% 0.21/0.50  fof(f663,plain,(
% 0.21/0.50    ~v3_pre_topc(u1_struct_0(sK1),sK0) | v1_tsep_1(sK1,sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f662,f46])).
% 0.21/0.50  fof(f662,plain,(
% 0.21/0.50    ~v3_pre_topc(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0) | v1_tsep_1(sK1,sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f661,f43])).
% 0.21/0.50  fof(f661,plain,(
% 0.21/0.50    ~v3_pre_topc(u1_struct_0(sK1),sK0) | ~m1_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | v1_tsep_1(sK1,sK0)),
% 0.21/0.50    inference(superposition,[],[f56,f531])).
% 0.21/0.50  fof(f531,plain,(
% 0.21/0.50    u1_struct_0(sK1) = sK2(sK0,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f526,f193])).
% 0.21/0.50  fof(f193,plain,(
% 0.21/0.50    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | u1_struct_0(sK1) = sK2(sK0,sK1)),
% 0.21/0.50    inference(resolution,[],[f102,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ~v1_tsep_1(sK1,sK0) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f39,f43])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k8_tmap_1(sK0,sK1) | ~v1_tsep_1(sK1,sK0) | ~m1_pre_topc(sK1,sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f18])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    v1_tsep_1(sK1,sK0) | u1_struct_0(sK1) = sK2(sK0,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f101,f46])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | u1_struct_0(sK1) = sK2(sK0,sK1) | v1_tsep_1(sK1,sK0)),
% 0.21/0.50    inference(resolution,[],[f55,f43])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | u1_struct_0(X1) = sK2(X0,X1) | v1_tsep_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f526,plain,(
% 0.21/0.50    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1) | u1_struct_0(sK1) = sK2(sK0,sK1)),
% 0.21/0.50    inference(superposition,[],[f118,f446])).
% 0.21/0.50  fof(f446,plain,(
% 0.21/0.50    u1_pre_topc(sK0) = u1_pre_topc(k8_tmap_1(sK0,sK1)) | u1_struct_0(sK1) = sK2(sK0,sK1)),
% 0.21/0.50    inference(resolution,[],[f397,f158])).
% 0.21/0.50  fof(f397,plain,(
% 0.21/0.50    r2_hidden(u1_struct_0(sK1),u1_pre_topc(sK0)) | u1_struct_0(sK1) = sK2(sK0,sK1)),
% 0.21/0.50    inference(resolution,[],[f196,f143])).
% 0.21/0.50  fof(f196,plain,(
% 0.21/0.50    v3_pre_topc(u1_struct_0(sK1),sK0) | u1_struct_0(sK1) = sK2(sK0,sK1)),
% 0.21/0.50    inference(subsumption_resolution,[],[f195,f46])).
% 0.21/0.50  fof(f195,plain,(
% 0.21/0.50    u1_struct_0(sK1) = sK2(sK0,sK1) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.50    inference(subsumption_resolution,[],[f194,f43])).
% 0.21/0.50  fof(f194,plain,(
% 0.21/0.50    u1_struct_0(sK1) = sK2(sK0,sK1) | ~m1_pre_topc(sK1,sK0) | v3_pre_topc(u1_struct_0(sK1),sK0) | ~l1_pre_topc(sK0)),
% 0.21/0.50    inference(resolution,[],[f102,f76])).
% 0.21/0.50  fof(f118,plain,(
% 0.21/0.50    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(k8_tmap_1(sK0,sK1)))),
% 0.21/0.50    inference(backward_demodulation,[],[f111,f117])).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))),
% 0.21/0.50    inference(subsumption_resolution,[],[f116,f44])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))),
% 0.21/0.50    inference(subsumption_resolution,[],[f115,f42])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    v2_struct_0(sK1) | v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))),
% 0.21/0.50    inference(subsumption_resolution,[],[f114,f46])).
% 0.21/0.50  fof(f114,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))),
% 0.21/0.50    inference(subsumption_resolution,[],[f113,f45])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK1) | v2_struct_0(sK0) | u1_struct_0(sK0) = u1_struct_0(k8_tmap_1(sK0,sK1))),
% 0.21/0.50    inference(resolution,[],[f64,f43])).
% 0.21/0.50  fof(f64,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X1) | v2_struct_0(X0) | u1_struct_0(X0) = u1_struct_0(k8_tmap_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f32])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1)))),
% 0.21/0.50    inference(subsumption_resolution,[],[f110,f100])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.21/0.50    inference(subsumption_resolution,[],[f99,f44])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    v2_struct_0(sK0) | l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.21/0.50    inference(subsumption_resolution,[],[f98,f46])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.21/0.50    inference(subsumption_resolution,[],[f97,f45])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | l1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.21/0.50    inference(resolution,[],[f68,f43])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | l1_pre_topc(k8_tmap_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1] : ((l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))) | (~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1] : ((m1_pre_topc(X1,X0) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k8_tmap_1(X0,X1)) & v2_pre_topc(k8_tmap_1(X0,X1)) & v1_pre_topc(k8_tmap_1(X0,X1))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k8_tmap_1)).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    ~l1_pre_topc(k8_tmap_1(sK0,sK1)) | k8_tmap_1(sK0,sK1) = g1_pre_topc(u1_struct_0(k8_tmap_1(sK0,sK1)),u1_pre_topc(k8_tmap_1(sK0,sK1)))),
% 0.21/0.50    inference(resolution,[],[f92,f51])).
% 0.21/0.50  fof(f92,plain,(
% 0.21/0.50    v1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.21/0.50    inference(subsumption_resolution,[],[f91,f44])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    v2_struct_0(sK0) | v1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.21/0.50    inference(subsumption_resolution,[],[f90,f46])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.21/0.50    inference(subsumption_resolution,[],[f89,f45])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_pre_topc(k8_tmap_1(sK0,sK1))),
% 0.21/0.50    inference(resolution,[],[f66,f43])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_pre_topc(X1,X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_pre_topc(k8_tmap_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f36])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v3_pre_topc(sK2(X0,X1),X0) | ~m1_pre_topc(X1,X0) | ~l1_pre_topc(X0) | v1_tsep_1(X1,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f294,plain,(
% 0.21/0.50    ~v1_tsep_1(sK1,sK0) | k8_tmap_1(sK0,sK1) != k6_tmap_1(sK0,u1_struct_0(sK0))),
% 0.21/0.50    inference(backward_demodulation,[],[f74,f292])).
% 0.21/0.50  fof(f725,plain,(
% 0.21/0.50    k8_tmap_1(sK0,sK1) = k6_tmap_1(sK0,u1_struct_0(sK0))),
% 0.21/0.50    inference(backward_demodulation,[],[f292,f705])).
% 0.21/0.50  fof(f705,plain,(
% 0.21/0.50    g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k8_tmap_1(sK0,sK1)),
% 0.21/0.50    inference(backward_demodulation,[],[f118,f703])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (8625)------------------------------
% 0.21/0.50  % (8625)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (8625)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (8625)Memory used [KB]: 2046
% 0.21/0.50  % (8625)Time elapsed: 0.096 s
% 0.21/0.50  % (8625)------------------------------
% 0.21/0.50  % (8625)------------------------------
% 0.21/0.50  % (8609)Refutation not found, incomplete strategy% (8609)------------------------------
% 0.21/0.50  % (8609)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (8609)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (8609)Memory used [KB]: 10618
% 0.21/0.50  % (8609)Time elapsed: 0.084 s
% 0.21/0.50  % (8609)------------------------------
% 0.21/0.50  % (8609)------------------------------
% 0.21/0.50  % (8607)Success in time 0.138 s
%------------------------------------------------------------------------------
