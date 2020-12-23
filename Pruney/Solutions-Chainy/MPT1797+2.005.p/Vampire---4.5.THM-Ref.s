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
% DateTime   : Thu Dec  3 13:19:30 EST 2020

% Result     : Theorem 1.66s
% Output     : Refutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :  370 (1454514 expanded)
%              Number of leaves         :   13 (286234 expanded)
%              Depth                    :  128
%              Number of atoms          : 1984 (7100541 expanded)
%              Number of equality atoms :  299 (427601 expanded)
%              Maximal formula depth    :   18 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4832,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4831,f3284])).

fof(f3284,plain,(
    v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f786,f3243])).

fof(f3243,plain,(
    k1_xboole_0 = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3242,f843])).

fof(f843,plain,(
    m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f842,f541])).

fof(f541,plain,(
    k7_tmap_1(sK0,sK1) = k6_partfun1(k2_struct_0(sK0)) ),
    inference(resolution,[],[f211,f197])).

fof(f197,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f46,f193])).

fof(f193,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f154,f50])).

fof(f50,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f154,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f49,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f49,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ( v3_pre_topc(X1,X0)
          <~> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) )
          & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0)
      & ~ v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0)
          & ~ v2_struct_0(X0) )
       => ! [X1] :
            ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
           => ( v3_pre_topc(X1,X0)
            <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
                & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
                & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
                & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
              & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1))
              & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
              & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_tmap_1)).

fof(f46,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f17])).

fof(f211,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k7_tmap_1(sK0,X0) = k6_partfun1(k2_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f199,f193])).

fof(f199,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0)) ) ),
    inference(backward_demodulation,[],[f111,f193])).

fof(f111,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f110,f49])).

fof(f110,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f89,f48])).

fof(f48,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f47,f63])).

fof(f63,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
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
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_tmap_1)).

fof(f47,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f842,plain,(
    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f837,f580])).

fof(f580,plain,(
    u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(sK0) ),
    inference(resolution,[],[f212,f197])).

fof(f212,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | u1_struct_0(k6_tmap_1(sK0,X1)) = k2_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f200,f193])).

fof(f200,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1)) ) ),
    inference(backward_demodulation,[],[f113,f193])).

fof(f113,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f112,f49])).

fof(f112,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f90,f48])).

fof(f90,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1)) ) ),
    inference(resolution,[],[f47,f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
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
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f837,plain,(
    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    inference(resolution,[],[f216,f197])).

fof(f216,plain,(
    ! [X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(k7_tmap_1(sK0,X13),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X13))))) ) ),
    inference(forward_demodulation,[],[f208,f193])).

fof(f208,plain,(
    ! [X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(k7_tmap_1(sK0,X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X13))))) ) ),
    inference(backward_demodulation,[],[f129,f193])).

fof(f129,plain,(
    ! [X13] :
      ( ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k7_tmap_1(sK0,X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X13))))) ) ),
    inference(subsumption_resolution,[],[f128,f49])).

fof(f128,plain,(
    ! [X13] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k7_tmap_1(sK0,X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X13))))) ) ),
    inference(subsumption_resolution,[],[f102,f48])).

fof(f102,plain,(
    ! [X13] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k7_tmap_1(sK0,X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X13))))) ) ),
    inference(resolution,[],[f47,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f3242,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(forward_demodulation,[],[f3241,f580])).

fof(f3241,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    inference(subsumption_resolution,[],[f3240,f786])).

fof(f3240,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | k1_xboole_0 = k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f3239,f580])).

fof(f3239,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    inference(subsumption_resolution,[],[f3238,f1264])).

fof(f1264,plain,
    ( ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1263,f786])).

fof(f1263,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(subsumption_resolution,[],[f1252,f843])).

fof(f1252,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(resolution,[],[f1251,f624])).

fof(f624,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f623,f585])).

fof(f585,plain,(
    k2_struct_0(sK0) = k2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f412,f580])).

fof(f412,plain,(
    u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f373,f50])).

fof(f373,plain,(
    l1_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f368,f51])).

fof(f368,plain,(
    l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f205,f197])).

fof(f205,plain,(
    ! [X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0)))
      | l1_pre_topc(k6_tmap_1(sK0,X10)) ) ),
    inference(backward_demodulation,[],[f123,f193])).

fof(f123,plain,(
    ! [X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
      | l1_pre_topc(k6_tmap_1(sK0,X10)) ) ),
    inference(subsumption_resolution,[],[f122,f49])).

fof(f122,plain,(
    ! [X10] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
      | l1_pre_topc(k6_tmap_1(sK0,X10)) ) ),
    inference(subsumption_resolution,[],[f99,f48])).

fof(f99,plain,(
    ! [X10] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
      | l1_pre_topc(k6_tmap_1(sK0,X10)) ) ),
    inference(resolution,[],[f47,f77])).

fof(f77,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f623,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f598,f551])).

fof(f551,plain,(
    v1_funct_1(k6_partfun1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f417,f541])).

fof(f417,plain,(
    v1_funct_1(k7_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f206,f197])).

fof(f206,plain,(
    ! [X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK0)))
      | v1_funct_1(k7_tmap_1(sK0,X11)) ) ),
    inference(backward_demodulation,[],[f125,f193])).

fof(f125,plain,(
    ! [X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_funct_1(k7_tmap_1(sK0,X11)) ) ),
    inference(subsumption_resolution,[],[f124,f49])).

fof(f124,plain,(
    ! [X11] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_funct_1(k7_tmap_1(sK0,X11)) ) ),
    inference(subsumption_resolution,[],[f100,f48])).

fof(f100,plain,(
    ! [X11] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_funct_1(k7_tmap_1(sK0,X11)) ) ),
    inference(resolution,[],[f47,f78])).

fof(f78,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_funct_1(k7_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f598,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f554,f585])).

fof(f554,plain,
    ( ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f553,f541])).

fof(f553,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f552,f541])).

fof(f552,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f550,f541])).

fof(f550,plain,
    ( ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f416,f541])).

fof(f416,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f415,f412])).

fof(f415,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f210,f412])).

fof(f210,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f194,f193])).

fof(f194,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f41,f193])).

fof(f41,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f1251,plain,
    ( v3_pre_topc(sK1,sK0)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1250,f800])).

fof(f800,plain,
    ( k6_tmap_1(sK0,sK1) != g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))
    | v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f213,f197])).

fof(f213,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | k6_tmap_1(sK0,X3) != g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))
      | v3_pre_topc(X3,sK0) ) ),
    inference(forward_demodulation,[],[f202,f193])).

fof(f202,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))
      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X3)
      | v3_pre_topc(X3,sK0) ) ),
    inference(backward_demodulation,[],[f117,f193])).

fof(f117,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X3)
      | v3_pre_topc(X3,sK0) ) ),
    inference(subsumption_resolution,[],[f116,f49])).

fof(f116,plain,(
    ! [X3] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X3)
      | v3_pre_topc(X3,sK0) ) ),
    inference(subsumption_resolution,[],[f92,f48])).

fof(f92,plain,(
    ! [X3] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X3)
      | v3_pre_topc(X3,sK0) ) ),
    inference(resolution,[],[f47,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1)
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
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
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).

fof(f1250,plain,
    ( v3_pre_topc(sK1,sK0)
    | k1_xboole_0 = k2_struct_0(sK0)
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f1249,f227])).

fof(f227,plain,(
    sK1 = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1) ),
    inference(resolution,[],[f197,f71])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

fof(f1249,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1),sK0)
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f1248,f551])).

fof(f1248,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1),sK0)
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f1247,f786])).

fof(f1247,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1),sK0)
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f1233,f843])).

fof(f1233,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1),sK0)
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f1224,f830])).

fof(f830,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f814,f197])).

fof(f814,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f214,f547])).

fof(f547,plain,
    ( v3_pre_topc(sK1,sK0)
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f44,f541])).

fof(f44,plain,
    ( v3_pre_topc(sK1,sK0)
    | v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f214,plain,(
    ! [X4] :
      ( ~ v3_pre_topc(X4,sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | k6_tmap_1(sK0,X4) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) ) ),
    inference(forward_demodulation,[],[f203,f193])).

fof(f203,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))
      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X4)
      | ~ v3_pre_topc(X4,sK0) ) ),
    inference(backward_demodulation,[],[f119,f193])).

fof(f119,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X4)
      | ~ v3_pre_topc(X4,sK0) ) ),
    inference(subsumption_resolution,[],[f118,f49])).

fof(f118,plain,(
    ! [X4] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X4)
      | ~ v3_pre_topc(X4,sK0) ) ),
    inference(subsumption_resolution,[],[f93,f48])).

fof(f93,plain,(
    ! [X4] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X4)
      | ~ v3_pre_topc(X4,sK0) ) ),
    inference(resolution,[],[f47,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f1224,plain,(
    ! [X20] :
      ( ~ v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1))
      | k1_xboole_0 = k2_struct_0(sK0)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_2(X20,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ v1_funct_1(X20)
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X20,sK1),sK0) ) ),
    inference(forward_demodulation,[],[f1223,f580])).

fof(f1223,plain,(
    ! [X20] :
      ( k1_xboole_0 = k2_struct_0(sK0)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_2(X20,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ v1_funct_1(X20)
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),sK0)
      | ~ v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f1222,f197])).

fof(f1222,plain,(
    ! [X20] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_xboole_0 = k2_struct_0(sK0)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_2(X20,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ v1_funct_1(X20)
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),sK0)
      | ~ v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f1221,f580])).

fof(f1221,plain,(
    ! [X20] :
      ( k1_xboole_0 = k2_struct_0(sK0)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_2(X20,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ v1_funct_1(X20)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),sK0)
      | ~ v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f1220,f585])).

fof(f1220,plain,(
    ! [X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_2(X20,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ v1_funct_1(X20)
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),sK0)
      | ~ v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f1219,f580])).

fof(f1219,plain,(
    ! [X20] :
      ( ~ v1_funct_2(X20,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ v1_funct_1(X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),sK0)
      | ~ v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f1218,f580])).

fof(f1218,plain,(
    ! [X20] :
      ( ~ v1_funct_1(X20)
      | ~ v1_funct_2(X20,k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),sK0)
      | ~ v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f1205,f368])).

fof(f1205,plain,(
    ! [X20] :
      ( ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X20)
      | ~ v1_funct_2(X20,k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),sK0)
      | ~ v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(resolution,[],[f317,f796])).

fof(f796,plain,(
    v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f795,f197])).

fof(f795,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f792])).

fof(f792,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) ),
    inference(superposition,[],[f209,f580])).

fof(f209,plain,(
    ! [X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X14))))
      | ~ m1_subset_1(X14,k1_zfmisc_1(k2_struct_0(sK0)))
      | v3_pre_topc(X14,k6_tmap_1(sK0,X14)) ) ),
    inference(backward_demodulation,[],[f131,f193])).

fof(f131,plain,(
    ! [X14] :
      ( ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X14))))
      | v3_pre_topc(X14,k6_tmap_1(sK0,X14)) ) ),
    inference(subsumption_resolution,[],[f130,f49])).

fof(f130,plain,(
    ! [X14] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X14))))
      | v3_pre_topc(X14,k6_tmap_1(sK0,X14)) ) ),
    inference(subsumption_resolution,[],[f103,f48])).

fof(f103,plain,(
    ! [X14] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X14))))
      | v3_pre_topc(X14,k6_tmap_1(sK0,X14)) ) ),
    inference(resolution,[],[f47,f81])).

fof(f81,plain,(
    ! [X2,X0] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2))))
      | v3_pre_topc(X2,k6_tmap_1(X0,X2)) ) ),
    inference(equality_resolution,[],[f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
      | X1 != X2
      | v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_pre_topc(X2,k6_tmap_1(X0,X1))
              | X1 != X2
              | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) )
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
         => ! [X2] :
              ( m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
             => ( X1 = X2
               => v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tmap_1)).

fof(f317,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(X2,X0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | k2_struct_0(X0) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X0),X1,X2),sK0)
      | ~ v5_pre_topc(X1,sK0,X0) ) ),
    inference(subsumption_resolution,[],[f235,f49])).

fof(f235,plain,(
    ! [X2,X0,X1] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X0),X1,X2),sK0)
      | ~ l1_pre_topc(sK0)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0))))
      | k2_struct_0(X0) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v3_pre_topc(X2,X0)
      | ~ v5_pre_topc(X1,sK0,X0) ) ),
    inference(superposition,[],[f52,f193])).

fof(f52,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
      | ~ v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
                    | ~ v3_pre_topc(X3,X1)
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) ) )
              | ( k2_struct_0(X0) != k1_xboole_0
                & k2_struct_0(X1) = k1_xboole_0 )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k2_struct_0(X1) = k1_xboole_0
                 => k2_struct_0(X0) = k1_xboole_0 )
               => ( v5_pre_topc(X2,X0,X1)
                <=> ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => ( v3_pre_topc(X3,X1)
                       => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_2)).

fof(f3238,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f3237,f551])).

fof(f3237,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f3236,f368])).

fof(f3236,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f3235,f341])).

fof(f341,plain,(
    v2_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f204,f197])).

fof(f204,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_pre_topc(k6_tmap_1(sK0,X7)) ) ),
    inference(backward_demodulation,[],[f121,f193])).

fof(f121,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_pre_topc(k6_tmap_1(sK0,X7)) ) ),
    inference(subsumption_resolution,[],[f120,f49])).

fof(f120,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_pre_topc(k6_tmap_1(sK0,X7)) ) ),
    inference(subsumption_resolution,[],[f96,f48])).

fof(f96,plain,(
    ! [X7] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | v2_pre_topc(k6_tmap_1(sK0,X7)) ) ),
    inference(resolution,[],[f47,f74])).

fof(f74,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1))
        & ~ v2_struct_0(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).

fof(f3235,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f3227])).

fof(f3227,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(resolution,[],[f3225,f2404])).

fof(f2404,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(X0,k6_tmap_1(sK0,sK1),X1)
      | ~ v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X0)
      | v5_pre_topc(X0,sK0,X1)
      | k1_xboole_0 = k2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f2403])).

fof(f2403,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,k6_tmap_1(sK0,sK1),X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1))))
      | v5_pre_topc(X0,sK0,X1)
      | k1_xboole_0 = k2_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f2402,f580])).

fof(f2402,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,k6_tmap_1(sK0,sK1),X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X1))))
      | v5_pre_topc(X0,sK0,X1)
      | k1_xboole_0 = k2_struct_0(sK0) ) ),
    inference(duplicate_literal_removal,[],[f2401])).

fof(f2401,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,k6_tmap_1(sK0,sK1),X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1))))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X1))))
      | v5_pre_topc(X0,sK0,X1)
      | k1_xboole_0 = k2_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f2398,f580])).

fof(f2398,plain,(
    ! [X0,X1] :
      ( ~ v5_pre_topc(X0,k6_tmap_1(sK0,sK1),X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X1))))
      | v5_pre_topc(X0,sK0,X1)
      | k1_xboole_0 = k2_struct_0(sK0) ) ),
    inference(superposition,[],[f330,f1265])).

fof(f1265,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f1253,f197])).

fof(f1253,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f1251,f214])).

fof(f330,plain,(
    ! [X142,X141] :
      ( ~ v5_pre_topc(X141,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X142)
      | ~ v2_pre_topc(X142)
      | ~ l1_pre_topc(X142)
      | ~ v1_funct_1(X141)
      | ~ v1_funct_2(X141,k2_struct_0(sK0),u1_struct_0(X142))
      | ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X142))))
      | ~ v1_funct_2(X141,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X142))
      | ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X142))))
      | v5_pre_topc(X141,sK0,X142) ) ),
    inference(subsumption_resolution,[],[f329,f49])).

fof(f329,plain,(
    ! [X142,X141] :
      ( ~ v5_pre_topc(X141,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X142)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(X142)
      | ~ l1_pre_topc(X142)
      | ~ v1_funct_1(X141)
      | ~ v1_funct_2(X141,k2_struct_0(sK0),u1_struct_0(X142))
      | ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X142))))
      | ~ v1_funct_2(X141,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X142))
      | ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X142))))
      | v5_pre_topc(X141,sK0,X142) ) ),
    inference(subsumption_resolution,[],[f312,f48])).

fof(f312,plain,(
    ! [X142,X141] :
      ( ~ v5_pre_topc(X141,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X142)
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(X142)
      | ~ l1_pre_topc(X142)
      | ~ v1_funct_1(X141)
      | ~ v1_funct_2(X141,k2_struct_0(sK0),u1_struct_0(X142))
      | ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X142))))
      | ~ v1_funct_2(X141,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X142))
      | ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X142))))
      | v5_pre_topc(X141,sK0,X142) ) ),
    inference(superposition,[],[f85,f193])).

fof(f85,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X3,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f83])).

fof(f83,plain,(
    ! [X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X3,X0,X1) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | X2 != X3
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ( v5_pre_topc(X2,X0,X1)
                  <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) )
                  | X2 != X3
                  | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                  | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                  | ~ v1_funct_1(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
                    & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
                    & v1_funct_1(X3) )
                 => ( X2 = X3
                   => ( v5_pre_topc(X2,X0,X1)
                    <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f3225,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f3224])).

fof(f3224,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(forward_demodulation,[],[f3223,f585])).

fof(f3223,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f3222,f843])).

fof(f3222,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f3221,f580])).

fof(f3221,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | k1_xboole_0 = k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f3220,f786])).

fof(f3220,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | k1_xboole_0 = k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f3219,f580])).

fof(f3219,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | k1_xboole_0 = k2_struct_0(sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f3218,f551])).

fof(f3218,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | k1_xboole_0 = k2_struct_0(sK0)
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f3217,f368])).

fof(f3217,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | k1_xboole_0 = k2_struct_0(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f3209])).

fof(f3209,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | k1_xboole_0 = k2_struct_0(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f3208,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_struct_0(X1) = k1_xboole_0
      | v3_pre_topc(sK2(X0,X1,X2),X1)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3208,plain,
    ( ~ v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3207,f551])).

fof(f3207,plain,
    ( ~ v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3206,f843])).

fof(f3206,plain,
    ( ~ v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f3205,f786])).

fof(f3205,plain,
    ( ~ v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(superposition,[],[f1182,f2615])).

fof(f2615,plain,
    ( sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))))
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(resolution,[],[f2567,f71])).

fof(f2567,plain,
    ( m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2566,f1264])).

fof(f2566,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f2565,f551])).

fof(f2565,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f2557,f843])).

fof(f2557,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f2454,f786])).

fof(f2454,plain,(
    ! [X5] :
      ( ~ v1_funct_2(X5,k2_struct_0(sK0),k2_struct_0(sK0))
      | k1_xboole_0 = k2_struct_0(sK0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_1(X5)
      | v5_pre_topc(X5,sK0,k6_tmap_1(sK0,sK1))
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5),k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f2453])).

fof(f2453,plain,(
    ! [X5] :
      ( k1_xboole_0 = k2_struct_0(sK0)
      | ~ v1_funct_2(X5,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_1(X5)
      | v5_pre_topc(X5,sK0,k6_tmap_1(sK0,sK1))
      | k1_xboole_0 = k2_struct_0(sK0)
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5),k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f2452,f585])).

fof(f2452,plain,(
    ! [X5] :
      ( ~ v1_funct_2(X5,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_1(X5)
      | v5_pre_topc(X5,sK0,k6_tmap_1(sK0,sK1))
      | k1_xboole_0 = k2_struct_0(sK0)
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5),k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f2451,f368])).

fof(f2451,plain,(
    ! [X5] :
      ( ~ v1_funct_2(X5,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X5)
      | v5_pre_topc(X5,sK0,k6_tmap_1(sK0,sK1))
      | k1_xboole_0 = k2_struct_0(sK0)
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5),k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(subsumption_resolution,[],[f2434,f341])).

fof(f2434,plain,(
    ! [X5] :
      ( ~ v1_funct_2(X5,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X5)
      | v5_pre_topc(X5,sK0,k6_tmap_1(sK0,sK1))
      | k1_xboole_0 = k2_struct_0(sK0)
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5),k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(superposition,[],[f2419,f580])).

fof(f2419,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X0)
      | v5_pre_topc(X0,sK0,X1)
      | k1_xboole_0 = k2_struct_0(sK0)
      | k2_struct_0(X1) = k1_xboole_0
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),X1,X0),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(duplicate_literal_removal,[],[f2418])).

fof(f2418,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X0)
      | v5_pre_topc(X0,sK0,X1)
      | k1_xboole_0 = k2_struct_0(sK0)
      | k2_struct_0(X1) = k1_xboole_0
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),X1,X0),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(forward_demodulation,[],[f2417,f580])).

fof(f2417,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X0)
      | v5_pre_topc(X0,sK0,X1)
      | k1_xboole_0 = k2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X1))))
      | k2_struct_0(X1) = k1_xboole_0
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),X1,X0),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(duplicate_literal_removal,[],[f2416])).

fof(f2416,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1))
      | ~ v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X0)
      | v5_pre_topc(X0,sK0,X1)
      | k1_xboole_0 = k2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X1))))
      | k2_struct_0(X1) = k1_xboole_0
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),X1,X0),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(forward_demodulation,[],[f2415,f580])).

fof(f2415,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X0)
      | v5_pre_topc(X0,sK0,X1)
      | k1_xboole_0 = k2_struct_0(sK0)
      | ~ v1_funct_2(X0,u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X1))))
      | k2_struct_0(X1) = k1_xboole_0
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),X1,X0),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(subsumption_resolution,[],[f2414,f368])).

fof(f2414,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X0)
      | v5_pre_topc(X0,sK0,X1)
      | k1_xboole_0 = k2_struct_0(sK0)
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_2(X0,u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X1))))
      | k2_struct_0(X1) = k1_xboole_0
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),X1,X0),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(duplicate_literal_removal,[],[f2405])).

fof(f2405,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X0)
      | v5_pre_topc(X0,sK0,X1)
      | k1_xboole_0 = k2_struct_0(sK0)
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X1))))
      | k2_struct_0(X1) = k1_xboole_0
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),X1,X0),k1_zfmisc_1(u1_struct_0(X1))) ) ),
    inference(resolution,[],[f2404,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_struct_0(X1) = k1_xboole_0
      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1182,plain,(
    ! [X5] :
      ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X5,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5)),k6_tmap_1(sK0,sK1))
      | ~ v1_funct_2(X5,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_1(X5)
      | v5_pre_topc(X5,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f1181,f1170])).

fof(f1170,plain,(
    ! [X5] :
      ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X5,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5)),k6_tmap_1(sK0,sK1))
      | ~ v1_funct_2(X5,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | k1_xboole_0 = k2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | v5_pre_topc(X5,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f1164,f368])).

fof(f1164,plain,(
    ! [X5] :
      ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X5,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5)),k6_tmap_1(sK0,sK1))
      | ~ v1_funct_2(X5,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | k1_xboole_0 = k2_struct_0(sK0)
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X5)
      | v5_pre_topc(X5,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(superposition,[],[f609,f580])).

fof(f609,plain,(
    ! [X47,X46] :
      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X46),k2_struct_0(sK0),X47,sK2(X46,k6_tmap_1(sK0,sK1),X47)),X46)
      | ~ v1_funct_2(X47,u1_struct_0(X46),k2_struct_0(sK0))
      | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),k2_struct_0(sK0))))
      | k1_xboole_0 = k2_struct_0(sK0)
      | ~ l1_pre_topc(X46)
      | ~ v1_funct_1(X47)
      | v5_pre_topc(X47,X46,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f608,f585])).

fof(f608,plain,(
    ! [X47,X46] :
      ( ~ v1_funct_2(X47,u1_struct_0(X46),k2_struct_0(sK0))
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X46),k2_struct_0(sK0),X47,sK2(X46,k6_tmap_1(sK0,sK1),X47)),X46)
      | k1_xboole_0 = k2_struct_0(sK0)
      | ~ l1_pre_topc(X46)
      | ~ v1_funct_1(X47)
      | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),k2_struct_0(k6_tmap_1(sK0,sK1)))))
      | v5_pre_topc(X47,X46,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f607,f585])).

fof(f607,plain,(
    ! [X47,X46] :
      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X46),k2_struct_0(sK0),X47,sK2(X46,k6_tmap_1(sK0,sK1),X47)),X46)
      | k1_xboole_0 = k2_struct_0(sK0)
      | ~ l1_pre_topc(X46)
      | ~ v1_funct_1(X47)
      | ~ v1_funct_2(X47,u1_struct_0(X46),k2_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),k2_struct_0(k6_tmap_1(sK0,sK1)))))
      | v5_pre_topc(X47,X46,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f589,f585])).

fof(f589,plain,(
    ! [X47,X46] :
      ( k1_xboole_0 = k2_struct_0(sK0)
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X46),k2_struct_0(k6_tmap_1(sK0,sK1)),X47,sK2(X46,k6_tmap_1(sK0,sK1),X47)),X46)
      | ~ l1_pre_topc(X46)
      | ~ v1_funct_1(X47)
      | ~ v1_funct_2(X47,u1_struct_0(X46),k2_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),k2_struct_0(k6_tmap_1(sK0,sK1)))))
      | v5_pre_topc(X47,X46,k6_tmap_1(sK0,sK1)) ) ),
    inference(backward_demodulation,[],[f526,f585])).

fof(f526,plain,(
    ! [X47,X46] :
      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X46),k2_struct_0(k6_tmap_1(sK0,sK1)),X47,sK2(X46,k6_tmap_1(sK0,sK1),X47)),X46)
      | ~ l1_pre_topc(X46)
      | ~ v1_funct_1(X47)
      | ~ v1_funct_2(X47,u1_struct_0(X46),k2_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),k2_struct_0(k6_tmap_1(sK0,sK1)))))
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | v5_pre_topc(X47,X46,k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f462,f368])).

fof(f462,plain,(
    ! [X47,X46] :
      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X46),k2_struct_0(k6_tmap_1(sK0,sK1)),X47,sK2(X46,k6_tmap_1(sK0,sK1),X47)),X46)
      | ~ l1_pre_topc(X46)
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X47)
      | ~ v1_funct_2(X47,u1_struct_0(X46),k2_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),k2_struct_0(k6_tmap_1(sK0,sK1)))))
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | v5_pre_topc(X47,X46,k6_tmap_1(sK0,sK1)) ) ),
    inference(superposition,[],[f55,f412])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_struct_0(X1) = k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f1181,plain,(
    ! [X5] :
      ( k1_xboole_0 != k2_struct_0(sK0)
      | ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X5,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5)),k6_tmap_1(sK0,sK1))
      | ~ v1_funct_2(X5,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_1(X5)
      | v5_pre_topc(X5,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f1180,f585])).

fof(f1180,plain,(
    ! [X5] :
      ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X5,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5)),k6_tmap_1(sK0,sK1))
      | ~ v1_funct_2(X5,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_1(X5)
      | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1))
      | v5_pre_topc(X5,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f1174,f368])).

fof(f1174,plain,(
    ! [X5] :
      ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X5,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5)),k6_tmap_1(sK0,sK1))
      | ~ v1_funct_2(X5,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X5)
      | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1))
      | v5_pre_topc(X5,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(superposition,[],[f614,f580])).

fof(f614,plain,(
    ! [X94,X95] :
      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X94),k2_struct_0(sK0),X95,sK2(X94,k6_tmap_1(sK0,sK1),X95)),X94)
      | ~ v1_funct_2(X95,u1_struct_0(X94),k2_struct_0(sK0))
      | ~ m1_subset_1(X95,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X94),k2_struct_0(sK0))))
      | ~ l1_pre_topc(X94)
      | ~ v1_funct_1(X95)
      | k1_xboole_0 != k2_struct_0(X94)
      | v5_pre_topc(X95,X94,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f613,f585])).

fof(f613,plain,(
    ! [X94,X95] :
      ( ~ v1_funct_2(X95,u1_struct_0(X94),k2_struct_0(sK0))
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X94),k2_struct_0(sK0),X95,sK2(X94,k6_tmap_1(sK0,sK1),X95)),X94)
      | ~ l1_pre_topc(X94)
      | ~ v1_funct_1(X95)
      | ~ m1_subset_1(X95,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X94),k2_struct_0(k6_tmap_1(sK0,sK1)))))
      | k1_xboole_0 != k2_struct_0(X94)
      | v5_pre_topc(X95,X94,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f593,f585])).

fof(f593,plain,(
    ! [X94,X95] :
      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X94),k2_struct_0(sK0),X95,sK2(X94,k6_tmap_1(sK0,sK1),X95)),X94)
      | ~ l1_pre_topc(X94)
      | ~ v1_funct_1(X95)
      | ~ v1_funct_2(X95,u1_struct_0(X94),k2_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ m1_subset_1(X95,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X94),k2_struct_0(k6_tmap_1(sK0,sK1)))))
      | k1_xboole_0 != k2_struct_0(X94)
      | v5_pre_topc(X95,X94,k6_tmap_1(sK0,sK1)) ) ),
    inference(backward_demodulation,[],[f532,f585])).

fof(f532,plain,(
    ! [X94,X95] :
      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X94),k2_struct_0(k6_tmap_1(sK0,sK1)),X95,sK2(X94,k6_tmap_1(sK0,sK1),X95)),X94)
      | ~ l1_pre_topc(X94)
      | ~ v1_funct_1(X95)
      | ~ v1_funct_2(X95,u1_struct_0(X94),k2_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ m1_subset_1(X95,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X94),k2_struct_0(k6_tmap_1(sK0,sK1)))))
      | k1_xboole_0 != k2_struct_0(X94)
      | v5_pre_topc(X95,X94,k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f484,f368])).

fof(f484,plain,(
    ! [X94,X95] :
      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X94),k2_struct_0(k6_tmap_1(sK0,sK1)),X95,sK2(X94,k6_tmap_1(sK0,sK1),X95)),X94)
      | ~ l1_pre_topc(X94)
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X95)
      | ~ v1_funct_2(X95,u1_struct_0(X94),k2_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ m1_subset_1(X95,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X94),k2_struct_0(k6_tmap_1(sK0,sK1)))))
      | k1_xboole_0 != k2_struct_0(X94)
      | v5_pre_topc(X95,X94,k6_tmap_1(sK0,sK1)) ) ),
    inference(superposition,[],[f59,f412])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_struct_0(X0) != k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f786,plain,(
    v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f785,f541])).

fof(f785,plain,(
    v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f780,f580])).

fof(f780,plain,(
    v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f215,f197])).

fof(f215,plain,(
    ! [X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_struct_0(sK0)))
      | v1_funct_2(k7_tmap_1(sK0,X12),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X12))) ) ),
    inference(forward_demodulation,[],[f207,f193])).

fof(f207,plain,(
    ! [X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(k2_struct_0(sK0)))
      | v1_funct_2(k7_tmap_1(sK0,X12),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X12))) ) ),
    inference(backward_demodulation,[],[f127,f193])).

fof(f127,plain,(
    ! [X12] :
      ( ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_funct_2(k7_tmap_1(sK0,X12),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X12))) ) ),
    inference(subsumption_resolution,[],[f126,f49])).

fof(f126,plain,(
    ! [X12] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_funct_2(k7_tmap_1(sK0,X12),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X12))) ) ),
    inference(subsumption_resolution,[],[f101,f48])).

fof(f101,plain,(
    ! [X12] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_funct_2(k7_tmap_1(sK0,X12),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X12))) ) ),
    inference(resolution,[],[f47,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f4831,plain,(
    ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f4830,f3271])).

fof(f3271,plain,(
    k1_xboole_0 = u1_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f580,f3243])).

fof(f4830,plain,(
    ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f4829,f3291])).

fof(f3291,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f843,f3243])).

fof(f4829,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    inference(forward_demodulation,[],[f4828,f3271])).

fof(f4828,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f4827,f3861])).

fof(f3861,plain,(
    ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f3860,f3284])).

fof(f3860,plain,
    ( ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    inference(subsumption_resolution,[],[f3858,f3291])).

fof(f3858,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    inference(resolution,[],[f3430,f3460])).

fof(f3460,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f3459,f3285])).

fof(f3285,plain,
    ( k6_tmap_1(sK0,sK1) != g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))
    | v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f800,f3243])).

fof(f3459,plain,
    ( v3_pre_topc(sK1,sK0)
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f3458,f3258])).

fof(f3258,plain,(
    sK1 = k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1) ),
    inference(backward_demodulation,[],[f227,f3243])).

fof(f3458,plain,
    ( v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),sK0)
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f3457,f3291])).

fof(f3457,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),sK0)
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f3382,f3284])).

fof(f3382,plain,
    ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),sK0)
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) ),
    inference(trivial_inequality_removal,[],[f3306])).

fof(f3306,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),sK0)
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) ),
    inference(backward_demodulation,[],[f1013,f3243])).

fof(f1013,plain,
    ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k1_xboole_0 != k2_struct_0(sK0)
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),sK0)
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) ),
    inference(inner_rewriting,[],[f1012])).

fof(f1012,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k2_struct_0(sK0)
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k2_struct_0(sK0)),sK1),sK0)
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f993,f551])).

fof(f993,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | k1_xboole_0 != k2_struct_0(sK0)
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k2_struct_0(sK0)),sK1),sK0)
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f970,f830])).

fof(f970,plain,(
    ! [X20] :
      ( ~ v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | ~ v1_funct_2(X20,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(X20)
      | k1_xboole_0 != k2_struct_0(sK0)
      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X20,sK1),sK0) ) ),
    inference(inner_rewriting,[],[f969])).

fof(f969,plain,(
    ! [X20] :
      ( v3_pre_topc(k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X20,sK1),sK0)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
      | ~ v1_funct_2(X20,k1_xboole_0,k2_struct_0(sK0))
      | ~ v1_funct_1(X20)
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f968,f580])).

fof(f968,plain,(
    ! [X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
      | ~ v1_funct_2(X20,k1_xboole_0,k2_struct_0(sK0))
      | ~ v1_funct_1(X20)
      | k1_xboole_0 != k2_struct_0(sK0)
      | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),sK0)
      | ~ v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f967,f197])).

fof(f967,plain,(
    ! [X20] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
      | ~ v1_funct_2(X20,k1_xboole_0,k2_struct_0(sK0))
      | ~ v1_funct_1(X20)
      | k1_xboole_0 != k2_struct_0(sK0)
      | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),sK0)
      | ~ v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f966,f580])).

fof(f966,plain,(
    ! [X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
      | ~ v1_funct_2(X20,k1_xboole_0,k2_struct_0(sK0))
      | ~ v1_funct_1(X20)
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),sK0)
      | ~ v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f965,f580])).

fof(f965,plain,(
    ! [X20] :
      ( ~ v1_funct_2(X20,k1_xboole_0,k2_struct_0(sK0))
      | ~ v1_funct_1(X20)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),sK0)
      | ~ v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f964,f580])).

fof(f964,plain,(
    ! [X20] :
      ( ~ v1_funct_1(X20)
      | ~ v1_funct_2(X20,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),sK0)
      | ~ v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f950,f368])).

fof(f950,plain,(
    ! [X20] :
      ( ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X20)
      | ~ v1_funct_2(X20,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),sK0)
      | ~ v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(resolution,[],[f322,f796])).

fof(f322,plain,(
    ! [X50,X48,X49] :
      ( ~ v3_pre_topc(X50,X48)
      | ~ l1_pre_topc(X48)
      | ~ v1_funct_1(X49)
      | ~ v1_funct_2(X49,k1_xboole_0,u1_struct_0(X48))
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X48))))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X48)))
      | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X48),X49,X50),sK0)
      | ~ v5_pre_topc(X49,sK0,X48) ) ),
    inference(inner_rewriting,[],[f321])).

fof(f321,plain,(
    ! [X50,X48,X49] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X48),X49,X50),sK0)
      | ~ l1_pre_topc(X48)
      | ~ v1_funct_1(X49)
      | ~ v1_funct_2(X49,k2_struct_0(sK0),u1_struct_0(X48))
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X48))))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X48)))
      | ~ v3_pre_topc(X50,X48)
      | ~ v5_pre_topc(X49,sK0,X48) ) ),
    inference(subsumption_resolution,[],[f257,f49])).

fof(f257,plain,(
    ! [X50,X48,X49] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X48),X49,X50),sK0)
      | ~ l1_pre_topc(sK0)
      | ~ l1_pre_topc(X48)
      | ~ v1_funct_1(X49)
      | ~ v1_funct_2(X49,k2_struct_0(sK0),u1_struct_0(X48))
      | ~ m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X48))))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X48)))
      | ~ v3_pre_topc(X50,X48)
      | ~ v5_pre_topc(X49,sK0,X48) ) ),
    inference(superposition,[],[f56,f193])).

fof(f56,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_struct_0(X0) != k1_xboole_0
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
      | ~ v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3430,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    inference(forward_demodulation,[],[f3429,f3243])).

fof(f3429,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f3281,f3243])).

fof(f3281,plain,
    ( ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(backward_demodulation,[],[f624,f3243])).

fof(f4827,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f4826,f3270])).

fof(f3270,plain,(
    v1_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f551,f3243])).

fof(f4826,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f4825,f368])).

fof(f4825,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f4817,f341])).

fof(f4817,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f4815,f3500])).

fof(f3500,plain,(
    ! [X142,X141] :
      ( ~ v5_pre_topc(X141,k6_tmap_1(sK0,sK1),X142)
      | ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X142))))
      | ~ v1_funct_2(X141,k1_xboole_0,u1_struct_0(X142))
      | ~ v2_pre_topc(X142)
      | ~ l1_pre_topc(X142)
      | ~ v1_funct_1(X141)
      | v5_pre_topc(X141,sK0,X142) ) ),
    inference(duplicate_literal_removal,[],[f3499])).

fof(f3499,plain,(
    ! [X142,X141] :
      ( ~ v1_funct_2(X141,k1_xboole_0,u1_struct_0(X142))
      | ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X142))))
      | ~ v5_pre_topc(X141,k6_tmap_1(sK0,sK1),X142)
      | ~ v1_funct_2(X141,k1_xboole_0,u1_struct_0(X142))
      | ~ v2_pre_topc(X142)
      | ~ l1_pre_topc(X142)
      | ~ v1_funct_1(X141)
      | v5_pre_topc(X141,sK0,X142) ) ),
    inference(forward_demodulation,[],[f3498,f3271])).

fof(f3498,plain,(
    ! [X142,X141] :
      ( ~ v1_funct_2(X141,u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X142))
      | ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X142))))
      | ~ v5_pre_topc(X141,k6_tmap_1(sK0,sK1),X142)
      | ~ v1_funct_2(X141,k1_xboole_0,u1_struct_0(X142))
      | ~ v2_pre_topc(X142)
      | ~ l1_pre_topc(X142)
      | ~ v1_funct_1(X141)
      | v5_pre_topc(X141,sK0,X142) ) ),
    inference(forward_demodulation,[],[f3497,f3469])).

fof(f3469,plain,(
    k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) ),
    inference(duplicate_literal_removal,[],[f3468])).

fof(f3468,plain,
    ( k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f3467,f3258])).

fof(f3467,plain,
    ( g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1))
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f3466,f3245])).

fof(f3245,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f197,f3243])).

fof(f3466,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1))
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) ),
    inference(forward_demodulation,[],[f3465,f3258])).

fof(f3465,plain,
    ( ~ m1_subset_1(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),k1_zfmisc_1(k1_xboole_0))
    | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1))
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f3464,f3291])).

fof(f3464,plain,
    ( ~ m1_subset_1(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),k1_zfmisc_1(k1_xboole_0))
    | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f3370,f3284])).

fof(f3370,plain,
    ( ~ m1_subset_1(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),k1_zfmisc_1(k1_xboole_0))
    | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) ),
    inference(trivial_inequality_removal,[],[f3319])).

fof(f3319,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),k1_zfmisc_1(k1_xboole_0))
    | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) ),
    inference(backward_demodulation,[],[f1129,f3243])).

fof(f1129,plain,
    ( ~ m1_subset_1(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),k1_zfmisc_1(k1_xboole_0))
    | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) ),
    inference(inner_rewriting,[],[f1128])).

fof(f1128,plain,
    ( ~ m1_subset_1(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k2_struct_0(sK0)),sK1),k1_zfmisc_1(k1_xboole_0))
    | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k2_struct_0(sK0)),sK1))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,k1_xboole_0)
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f1109,f551])).

fof(f1109,plain,
    ( ~ m1_subset_1(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k2_struct_0(sK0)),sK1),k1_zfmisc_1(k1_xboole_0))
    | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k2_struct_0(sK0)),sK1))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,k1_xboole_0)
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f1070,f830])).

fof(f1070,plain,(
    ! [X20] :
      ( ~ v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(k8_relset_1(k1_xboole_0,k1_xboole_0,X20,sK1),k1_zfmisc_1(k1_xboole_0))
      | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k1_xboole_0,X20,sK1))
      | ~ v1_funct_2(X20,k1_xboole_0,k1_xboole_0)
      | ~ v1_funct_1(X20)
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ) ),
    inference(inner_rewriting,[],[f1069])).

fof(f1069,plain,(
    ! [X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
      | ~ m1_subset_1(k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X20,sK1),k1_zfmisc_1(k1_xboole_0))
      | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X20,sK1))
      | ~ v1_funct_2(X20,k1_xboole_0,k2_struct_0(sK0))
      | ~ v1_funct_1(X20)
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f1068,f580])).

fof(f1068,plain,(
    ! [X20] :
      ( ~ m1_subset_1(k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X20,sK1),k1_zfmisc_1(k1_xboole_0))
      | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X20,sK1))
      | ~ v1_funct_2(X20,k1_xboole_0,k2_struct_0(sK0))
      | ~ v1_funct_1(X20)
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | ~ v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f1067,f197])).

fof(f1067,plain,(
    ! [X20] :
      ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X20,sK1),k1_zfmisc_1(k1_xboole_0))
      | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X20,sK1))
      | ~ v1_funct_2(X20,k1_xboole_0,k2_struct_0(sK0))
      | ~ v1_funct_1(X20)
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | ~ v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f1066,f580])).

fof(f1066,plain,(
    ! [X20] :
      ( ~ m1_subset_1(k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X20,sK1),k1_zfmisc_1(k1_xboole_0))
      | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X20,sK1))
      | ~ v1_funct_2(X20,k1_xboole_0,k2_struct_0(sK0))
      | ~ v1_funct_1(X20)
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | ~ v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f1065,f580])).

fof(f1065,plain,(
    ! [X20] :
      ( g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X20,sK1))
      | ~ v1_funct_2(X20,k1_xboole_0,k2_struct_0(sK0))
      | ~ m1_subset_1(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(X20)
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | ~ v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f1064,f580])).

fof(f1064,plain,(
    ! [X20] :
      ( ~ v1_funct_2(X20,k1_xboole_0,k2_struct_0(sK0))
      | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1))
      | ~ m1_subset_1(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(X20)
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | ~ v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f1063,f580])).

fof(f1063,plain,(
    ! [X20] :
      ( ~ v1_funct_2(X20,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))
      | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1))
      | ~ m1_subset_1(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(X20)
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | ~ v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f1048,f368])).

fof(f1048,plain,(
    ! [X20] :
      ( ~ v1_funct_2(X20,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))
      | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1))
      | ~ m1_subset_1(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),k1_zfmisc_1(k1_xboole_0))
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X20)
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | ~ m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | ~ v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(resolution,[],[f828,f796])).

fof(f828,plain,(
    ! [X6,X4,X5] :
      ( ~ v3_pre_topc(X6,X4)
      | ~ v1_funct_2(X5,k1_xboole_0,u1_struct_0(X4))
      | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,u1_struct_0(X4),X5,X6))
      | ~ m1_subset_1(k8_relset_1(k1_xboole_0,u1_struct_0(X4),X5,X6),k1_zfmisc_1(k1_xboole_0))
      | ~ l1_pre_topc(X4)
      | ~ v1_funct_1(X5)
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X4))))
      | ~ v5_pre_topc(X5,sK0,X4) ) ),
    inference(inner_rewriting,[],[f827])).

fof(f827,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X4))))
      | ~ v1_funct_2(X5,k2_struct_0(sK0),u1_struct_0(X4))
      | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k2_struct_0(sK0),u1_struct_0(X4),X5,X6))
      | ~ m1_subset_1(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X4),X5,X6),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(X4)
      | ~ v1_funct_1(X5)
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ v3_pre_topc(X6,X4)
      | ~ v5_pre_topc(X5,sK0,X4) ) ),
    inference(forward_demodulation,[],[f826,f193])).

fof(f826,plain,(
    ! [X6,X4,X5] :
      ( ~ v1_funct_2(X5,k2_struct_0(sK0),u1_struct_0(X4))
      | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k2_struct_0(sK0),u1_struct_0(X4),X5,X6))
      | ~ m1_subset_1(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X4),X5,X6),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ v3_pre_topc(X6,X4)
      | ~ v5_pre_topc(X5,sK0,X4) ) ),
    inference(forward_demodulation,[],[f825,f193])).

fof(f825,plain,(
    ! [X6,X4,X5] :
      ( g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k2_struct_0(sK0),u1_struct_0(X4),X5,X6))
      | ~ m1_subset_1(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X4),X5,X6),k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(X4)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ v3_pre_topc(X6,X4)
      | ~ v5_pre_topc(X5,sK0,X4) ) ),
    inference(forward_demodulation,[],[f824,f193])).

fof(f824,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X4),X5,X6),k1_zfmisc_1(k2_struct_0(sK0)))
      | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(X4),X5,X6))
      | ~ l1_pre_topc(X4)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ v3_pre_topc(X6,X4)
      | ~ v5_pre_topc(X5,sK0,X4) ) ),
    inference(forward_demodulation,[],[f823,f193])).

fof(f823,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X4),X5,X6),k1_zfmisc_1(k2_struct_0(sK0)))
      | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(X4),X5,X6))
      | ~ l1_pre_topc(X4)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ v3_pre_topc(X6,X4)
      | ~ v5_pre_topc(X5,sK0,X4) ) ),
    inference(subsumption_resolution,[],[f811,f49])).

fof(f811,plain,(
    ! [X6,X4,X5] :
      ( ~ m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X4),X5,X6),k1_zfmisc_1(k2_struct_0(sK0)))
      | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(X4),X5,X6))
      | ~ l1_pre_topc(sK0)
      | ~ l1_pre_topc(X4)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4))))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4)))
      | ~ v3_pre_topc(X6,X4)
      | ~ v5_pre_topc(X5,sK0,X4) ) ),
    inference(resolution,[],[f214,f56])).

fof(f3497,plain,(
    ! [X142,X141] :
      ( ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X142))))
      | ~ v5_pre_topc(X141,k6_tmap_1(sK0,sK1),X142)
      | ~ v1_funct_2(X141,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X142))
      | ~ v1_funct_2(X141,k1_xboole_0,u1_struct_0(X142))
      | ~ v2_pre_topc(X142)
      | ~ l1_pre_topc(X142)
      | ~ v1_funct_1(X141)
      | v5_pre_topc(X141,sK0,X142) ) ),
    inference(duplicate_literal_removal,[],[f3496])).

fof(f3496,plain,(
    ! [X142,X141] :
      ( ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X142))))
      | ~ v5_pre_topc(X141,k6_tmap_1(sK0,sK1),X142)
      | ~ v1_funct_2(X141,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X142))
      | ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X142))))
      | ~ v1_funct_2(X141,k1_xboole_0,u1_struct_0(X142))
      | ~ v2_pre_topc(X142)
      | ~ l1_pre_topc(X142)
      | ~ v1_funct_1(X141)
      | v5_pre_topc(X141,sK0,X142) ) ),
    inference(forward_demodulation,[],[f3495,f3271])).

fof(f3495,plain,(
    ! [X142,X141] :
      ( ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X142))))
      | ~ v5_pre_topc(X141,k6_tmap_1(sK0,sK1),X142)
      | ~ v1_funct_2(X141,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X142))
      | ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X142))))
      | ~ v1_funct_2(X141,k1_xboole_0,u1_struct_0(X142))
      | ~ v2_pre_topc(X142)
      | ~ l1_pre_topc(X142)
      | ~ v1_funct_1(X141)
      | v5_pre_topc(X141,sK0,X142) ) ),
    inference(forward_demodulation,[],[f3482,f3469])).

fof(f3482,plain,(
    ! [X142,X141] :
      ( ~ v5_pre_topc(X141,k6_tmap_1(sK0,sK1),X142)
      | ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X142))))
      | ~ v1_funct_2(X141,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X142))
      | ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X142))))
      | ~ v1_funct_2(X141,k1_xboole_0,u1_struct_0(X142))
      | ~ v2_pre_topc(X142)
      | ~ l1_pre_topc(X142)
      | ~ v1_funct_1(X141)
      | v5_pre_topc(X141,sK0,X142) ) ),
    inference(backward_demodulation,[],[f3419,f3469])).

fof(f3419,plain,(
    ! [X142,X141] :
      ( ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X142))))
      | ~ v1_funct_2(X141,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X142))
      | ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X142))))
      | ~ v1_funct_2(X141,k1_xboole_0,u1_struct_0(X142))
      | ~ v5_pre_topc(X141,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X142)
      | ~ v2_pre_topc(X142)
      | ~ l1_pre_topc(X142)
      | ~ v1_funct_1(X141)
      | v5_pre_topc(X141,sK0,X142) ) ),
    inference(forward_demodulation,[],[f3418,f3243])).

fof(f3418,plain,(
    ! [X142,X141] :
      ( ~ v1_funct_2(X141,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X142))
      | ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X142))))
      | ~ v1_funct_2(X141,k1_xboole_0,u1_struct_0(X142))
      | ~ v5_pre_topc(X141,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X142)
      | ~ v2_pre_topc(X142)
      | ~ l1_pre_topc(X142)
      | ~ v1_funct_1(X141)
      | ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X142))))
      | v5_pre_topc(X141,sK0,X142) ) ),
    inference(forward_demodulation,[],[f3417,f3243])).

fof(f3417,plain,(
    ! [X142,X141] :
      ( ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X142))))
      | ~ v1_funct_2(X141,k1_xboole_0,u1_struct_0(X142))
      | ~ v5_pre_topc(X141,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X142)
      | ~ v2_pre_topc(X142)
      | ~ l1_pre_topc(X142)
      | ~ v1_funct_1(X141)
      | ~ v1_funct_2(X141,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X142))
      | ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X142))))
      | v5_pre_topc(X141,sK0,X142) ) ),
    inference(forward_demodulation,[],[f3416,f3243])).

fof(f3416,plain,(
    ! [X142,X141] :
      ( ~ v1_funct_2(X141,k1_xboole_0,u1_struct_0(X142))
      | ~ v5_pre_topc(X141,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X142)
      | ~ v2_pre_topc(X142)
      | ~ l1_pre_topc(X142)
      | ~ v1_funct_1(X141)
      | ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X142))))
      | ~ v1_funct_2(X141,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X142))
      | ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X142))))
      | v5_pre_topc(X141,sK0,X142) ) ),
    inference(forward_demodulation,[],[f3266,f3243])).

fof(f3266,plain,(
    ! [X142,X141] :
      ( ~ v5_pre_topc(X141,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X142)
      | ~ v2_pre_topc(X142)
      | ~ l1_pre_topc(X142)
      | ~ v1_funct_1(X141)
      | ~ v1_funct_2(X141,k2_struct_0(sK0),u1_struct_0(X142))
      | ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X142))))
      | ~ v1_funct_2(X141,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X142))
      | ~ m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X142))))
      | v5_pre_topc(X141,sK0,X142) ) ),
    inference(backward_demodulation,[],[f330,f3243])).

fof(f4815,plain,(
    v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f4814,f3291])).

fof(f4814,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f4813,f3271])).

fof(f4813,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    inference(subsumption_resolution,[],[f4812,f3284])).

fof(f4812,plain,
    ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    inference(forward_demodulation,[],[f4811,f3271])).

fof(f4811,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    inference(subsumption_resolution,[],[f4810,f3272])).

fof(f3272,plain,(
    k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f585,f3243])).

fof(f4810,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f4809,f3270])).

fof(f4809,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f4807,f368])).

fof(f4807,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f4805])).

fof(f4805,plain,
    ( v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f4803,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_struct_0(X0) != k1_xboole_0
      | v3_pre_topc(sK2(X0,X1,X2),X1)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f4803,plain,
    ( ~ v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k6_tmap_1(sK0,sK1))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f4802,f3291])).

fof(f4802,plain,
    ( ~ v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f4801,f3284])).

fof(f4801,plain,
    ( ~ v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f4799,f3270])).

fof(f4799,plain,
    ( ~ v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ),
    inference(superposition,[],[f3373,f4396])).

fof(f4396,plain,(
    sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)) = k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))) ),
    inference(resolution,[],[f4386,f71])).

fof(f4386,plain,(
    m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f4385,f3861])).

fof(f4385,plain,
    ( m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f4384,f3270])).

fof(f4384,plain,
    ( m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f4382,f3291])).

fof(f4382,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f4345,f3284])).

fof(f4345,plain,(
    ! [X5] :
      ( ~ v1_funct_2(X5,k1_xboole_0,k1_xboole_0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5),k1_zfmisc_1(k1_xboole_0))
      | ~ v1_funct_1(X5)
      | v5_pre_topc(X5,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f4344,f368])).

fof(f4344,plain,(
    ! [X5] :
      ( ~ v1_funct_2(X5,k1_xboole_0,k1_xboole_0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5),k1_zfmisc_1(k1_xboole_0))
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X5)
      | v5_pre_topc(X5,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f4341,f341])).

fof(f4341,plain,(
    ! [X5] :
      ( ~ v1_funct_2(X5,k1_xboole_0,k1_xboole_0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5),k1_zfmisc_1(k1_xboole_0))
      | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X5)
      | v5_pre_topc(X5,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(superposition,[],[f3594,f3271])).

fof(f3594,plain,(
    ! [X6,X7] :
      ( ~ v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6))))
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),X6,X7),k1_zfmisc_1(u1_struct_0(X6)))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X7)
      | v5_pre_topc(X7,sK0,X6) ) ),
    inference(forward_demodulation,[],[f3593,f3469])).

fof(f3593,plain,(
    ! [X6,X7] :
      ( m1_subset_1(sK2(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6))))
      | ~ v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X7)
      | v5_pre_topc(X7,sK0,X6) ) ),
    inference(forward_demodulation,[],[f3592,f3243])).

fof(f3592,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6))))
      | ~ v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X7)
      | v5_pre_topc(X7,sK0,X6)
      | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(subsumption_resolution,[],[f3591,f3272])).

fof(f3591,plain,(
    ! [X6,X7] :
      ( k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6))))
      | ~ v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X7)
      | v5_pre_topc(X7,sK0,X6)
      | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(forward_demodulation,[],[f3590,f3469])).

fof(f3590,plain,(
    ! [X6,X7] :
      ( k1_xboole_0 != k2_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6))))
      | ~ v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X7)
      | v5_pre_topc(X7,sK0,X6)
      | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(forward_demodulation,[],[f3589,f3243])).

fof(f3589,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6))))
      | ~ v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X7)
      | v5_pre_topc(X7,sK0,X6)
      | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(subsumption_resolution,[],[f3588,f368])).

fof(f3588,plain,(
    ! [X6,X7] :
      ( ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6))))
      | ~ v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X7)
      | v5_pre_topc(X7,sK0,X6)
      | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(forward_demodulation,[],[f3587,f3469])).

fof(f3587,plain,(
    ! [X6,X7] :
      ( ~ l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6))))
      | ~ v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X7)
      | v5_pre_topc(X7,sK0,X6)
      | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(forward_demodulation,[],[f3586,f3243])).

fof(f3586,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6))))
      | ~ v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X7)
      | v5_pre_topc(X7,sK0,X6)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(duplicate_literal_removal,[],[f3585])).

fof(f3585,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6))))
      | ~ v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6))))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X7)
      | v5_pre_topc(X7,sK0,X6)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(forward_demodulation,[],[f3584,f3271])).

fof(f3584,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X6))))
      | ~ v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6))))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X7)
      | v5_pre_topc(X7,sK0,X6)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(forward_demodulation,[],[f3583,f3469])).

fof(f3583,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X6))))
      | ~ v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6))))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X7)
      | v5_pre_topc(X7,sK0,X6)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(forward_demodulation,[],[f3582,f3243])).

fof(f3582,plain,(
    ! [X6,X7] :
      ( ~ v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6))))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6))))
      | v5_pre_topc(X7,sK0,X6)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(duplicate_literal_removal,[],[f3581])).

fof(f3581,plain,(
    ! [X6,X7] :
      ( ~ v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6))))
      | ~ v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6))))
      | v5_pre_topc(X7,sK0,X6)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(forward_demodulation,[],[f3580,f3271])).

fof(f3580,plain,(
    ! [X6,X7] :
      ( ~ v1_funct_2(X7,u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X6))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6))))
      | ~ v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6))))
      | v5_pre_topc(X7,sK0,X6)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(forward_demodulation,[],[f3579,f3469])).

fof(f3579,plain,(
    ! [X6,X7] :
      ( ~ v1_funct_2(X7,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X6))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6))))
      | ~ v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6))))
      | v5_pre_topc(X7,sK0,X6)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(forward_demodulation,[],[f3578,f3243])).

fof(f3578,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6))))
      | ~ v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6))))
      | v5_pre_topc(X7,sK0,X6)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(forward_demodulation,[],[f3349,f3243])).

fof(f3349,plain,(
    ! [X6,X7] :
      ( ~ v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6))
      | ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X7)
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X6))))
      | ~ v1_funct_2(X7,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6))))
      | v5_pre_topc(X7,sK0,X6)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(backward_demodulation,[],[f2399,f3243])).

fof(f2399,plain,(
    ! [X6,X7] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,k2_struct_0(sK0),u1_struct_0(X6))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X6))))
      | ~ v1_funct_2(X7,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6))))
      | v5_pre_topc(X7,sK0,X6)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(duplicate_literal_removal,[],[f2389])).

fof(f2389,plain,(
    ! [X6,X7] :
      ( ~ v2_pre_topc(X6)
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,k2_struct_0(sK0),u1_struct_0(X6))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X6))))
      | ~ v1_funct_2(X7,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6))))
      | v5_pre_topc(X7,sK0,X6)
      | ~ l1_pre_topc(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | ~ l1_pre_topc(X6)
      | ~ v1_funct_1(X7)
      | ~ v1_funct_2(X7,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6))
      | ~ m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6))))
      | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)))
      | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6))) ) ),
    inference(resolution,[],[f330,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_struct_0(X0) != k1_xboole_0
      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f3373,plain,(
    ! [X5] :
      ( ~ v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X5,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5)),k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,k1_xboole_0,k1_xboole_0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | v5_pre_topc(X5,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(trivial_inequality_removal,[],[f3316])).

fof(f3316,plain,(
    ! [X5] :
      ( k1_xboole_0 != k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X5,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5)),k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,k1_xboole_0,k1_xboole_0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | v5_pre_topc(X5,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(backward_demodulation,[],[f1089,f3243])).

fof(f1089,plain,(
    ! [X5] :
      ( ~ v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X5,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5)),k6_tmap_1(sK0,sK1))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,k1_xboole_0,k1_xboole_0)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
      | v5_pre_topc(X5,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(inner_rewriting,[],[f1088])).

fof(f1088,plain,(
    ! [X5] :
      ( ~ v3_pre_topc(k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X5,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5)),k6_tmap_1(sK0,sK1))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,k1_xboole_0,k2_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
      | v5_pre_topc(X5,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f1086,f368])).

fof(f1086,plain,(
    ! [X5] :
      ( ~ v3_pre_topc(k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X5,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5)),k6_tmap_1(sK0,sK1))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X5)
      | ~ v1_funct_2(X5,k1_xboole_0,k2_struct_0(sK0))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0))))
      | v5_pre_topc(X5,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(superposition,[],[f592,f580])).

fof(f592,plain,(
    ! [X92,X93] :
      ( ~ v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X92),X93,sK2(k6_tmap_1(sK0,sK1),X92,X93)),k6_tmap_1(sK0,sK1))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ l1_pre_topc(X92)
      | ~ v1_funct_1(X93)
      | ~ v1_funct_2(X93,k1_xboole_0,u1_struct_0(X92))
      | ~ m1_subset_1(X93,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X92))))
      | v5_pre_topc(X93,k6_tmap_1(sK0,sK1),X92) ) ),
    inference(backward_demodulation,[],[f531,f585])).

fof(f531,plain,(
    ! [X92,X93] :
      ( ~ v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X92),X93,sK2(k6_tmap_1(sK0,sK1),X92,X93)),k6_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(X92)
      | ~ v1_funct_1(X93)
      | ~ v1_funct_2(X93,k1_xboole_0,u1_struct_0(X92))
      | ~ m1_subset_1(X93,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X92))))
      | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1))
      | v5_pre_topc(X93,k6_tmap_1(sK0,sK1),X92) ) ),
    inference(inner_rewriting,[],[f530])).

fof(f530,plain,(
    ! [X92,X93] :
      ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X92),X93,sK2(k6_tmap_1(sK0,sK1),X92,X93)),k6_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(X92)
      | ~ v1_funct_1(X93)
      | ~ v1_funct_2(X93,k2_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X92))
      | ~ m1_subset_1(X93,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X92))))
      | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1))
      | v5_pre_topc(X93,k6_tmap_1(sK0,sK1),X92) ) ),
    inference(subsumption_resolution,[],[f483,f368])).

fof(f483,plain,(
    ! [X92,X93] :
      ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X92),X93,sK2(k6_tmap_1(sK0,sK1),X92,X93)),k6_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(X92)
      | ~ v1_funct_1(X93)
      | ~ v1_funct_2(X93,k2_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X92))
      | ~ m1_subset_1(X93,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X92))))
      | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1))
      | v5_pre_topc(X93,k6_tmap_1(sK0,sK1),X92) ) ),
    inference(superposition,[],[f59,f412])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 14:42:52 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.19/0.40  % (7568)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.19/0.42  % (7583)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.19/0.43  % (7572)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.19/0.45  % (7579)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.19/0.46  % (7567)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.46  % (7567)Refutation not found, incomplete strategy% (7567)------------------------------
% 0.19/0.46  % (7567)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.46  % (7573)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.19/0.46  % (7575)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.19/0.46  % (7567)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.46  
% 0.19/0.46  % (7567)Memory used [KB]: 10618
% 0.19/0.46  % (7567)Time elapsed: 0.053 s
% 0.19/0.46  % (7567)------------------------------
% 0.19/0.46  % (7567)------------------------------
% 0.19/0.47  % (7586)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.19/0.47  % (7586)Refutation not found, incomplete strategy% (7586)------------------------------
% 0.19/0.47  % (7586)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.47  % (7586)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.47  
% 0.19/0.47  % (7586)Memory used [KB]: 10618
% 0.19/0.47  % (7586)Time elapsed: 0.082 s
% 0.19/0.47  % (7586)------------------------------
% 0.19/0.47  % (7586)------------------------------
% 0.19/0.48  % (7571)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.48  % (7578)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.19/0.48  % (7584)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.19/0.48  % (7581)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.19/0.48  % (7566)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.19/0.48  % (7578)Refutation not found, incomplete strategy% (7578)------------------------------
% 0.19/0.48  % (7578)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (7578)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.48  
% 0.19/0.48  % (7578)Memory used [KB]: 6140
% 0.19/0.48  % (7578)Time elapsed: 0.071 s
% 0.19/0.48  % (7578)------------------------------
% 0.19/0.48  % (7578)------------------------------
% 0.19/0.48  % (7566)Refutation not found, incomplete strategy% (7566)------------------------------
% 0.19/0.48  % (7566)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.48  % (7566)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.48  
% 0.19/0.48  % (7566)Memory used [KB]: 6268
% 0.19/0.48  % (7566)Time elapsed: 0.076 s
% 0.19/0.48  % (7566)------------------------------
% 0.19/0.48  % (7566)------------------------------
% 0.19/0.48  % (7569)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.19/0.48  % (7570)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.19/0.48  % (7574)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.19/0.49  % (7580)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.19/0.49  % (7582)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.19/0.50  % (7576)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.19/0.50  % (7577)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.19/0.50  % (7576)Refutation not found, incomplete strategy% (7576)------------------------------
% 0.19/0.50  % (7576)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.50  % (7576)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.50  
% 0.19/0.50  % (7576)Memory used [KB]: 6140
% 0.19/0.50  % (7576)Time elapsed: 0.080 s
% 0.19/0.50  % (7576)------------------------------
% 0.19/0.50  % (7576)------------------------------
% 0.19/0.51  % (7585)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 1.66/0.59  % (7579)Refutation found. Thanks to Tanya!
% 1.66/0.59  % SZS status Theorem for theBenchmark
% 1.66/0.60  % SZS output start Proof for theBenchmark
% 1.66/0.60  fof(f4832,plain,(
% 1.66/0.60    $false),
% 1.66/0.60    inference(subsumption_resolution,[],[f4831,f3284])).
% 1.66/0.60  fof(f3284,plain,(
% 1.66/0.60    v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)),
% 1.66/0.60    inference(backward_demodulation,[],[f786,f3243])).
% 1.66/0.60  fof(f3243,plain,(
% 1.66/0.60    k1_xboole_0 = k2_struct_0(sK0)),
% 1.66/0.60    inference(subsumption_resolution,[],[f3242,f843])).
% 1.66/0.60  fof(f843,plain,(
% 1.66/0.60    m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))),
% 1.66/0.60    inference(forward_demodulation,[],[f842,f541])).
% 1.66/0.60  fof(f541,plain,(
% 1.66/0.60    k7_tmap_1(sK0,sK1) = k6_partfun1(k2_struct_0(sK0))),
% 1.66/0.60    inference(resolution,[],[f211,f197])).
% 1.66/0.60  fof(f197,plain,(
% 1.66/0.60    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.66/0.60    inference(backward_demodulation,[],[f46,f193])).
% 1.66/0.60  fof(f193,plain,(
% 1.66/0.60    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.66/0.60    inference(resolution,[],[f154,f50])).
% 1.66/0.60  fof(f50,plain,(
% 1.66/0.60    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f18])).
% 1.66/0.60  fof(f18,plain,(
% 1.66/0.60    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.66/0.60    inference(ennf_transformation,[],[f2])).
% 1.66/0.60  fof(f2,axiom,(
% 1.66/0.60    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.66/0.60  fof(f154,plain,(
% 1.66/0.60    l1_struct_0(sK0)),
% 1.66/0.60    inference(resolution,[],[f49,f51])).
% 1.66/0.60  fof(f51,plain,(
% 1.66/0.60    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f19])).
% 1.66/0.60  fof(f19,plain,(
% 1.66/0.60    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.66/0.60    inference(ennf_transformation,[],[f3])).
% 1.66/0.60  fof(f3,axiom,(
% 1.66/0.60    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.66/0.60  fof(f49,plain,(
% 1.66/0.60    l1_pre_topc(sK0)),
% 1.66/0.60    inference(cnf_transformation,[],[f17])).
% 1.66/0.60  fof(f17,plain,(
% 1.66/0.60    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.66/0.60    inference(flattening,[],[f16])).
% 1.66/0.60  fof(f16,plain,(
% 1.66/0.60    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.66/0.60    inference(ennf_transformation,[],[f15])).
% 1.66/0.60  fof(f15,negated_conjecture,(
% 1.66/0.60    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 1.66/0.60    inference(negated_conjecture,[],[f14])).
% 1.66/0.60  fof(f14,conjecture,(
% 1.66/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_tmap_1)).
% 1.66/0.60  fof(f46,plain,(
% 1.66/0.60    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.66/0.60    inference(cnf_transformation,[],[f17])).
% 1.66/0.60  fof(f211,plain,(
% 1.66/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k7_tmap_1(sK0,X0) = k6_partfun1(k2_struct_0(sK0))) )),
% 1.66/0.60    inference(forward_demodulation,[],[f199,f193])).
% 1.66/0.60  fof(f199,plain,(
% 1.66/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0))) )),
% 1.66/0.60    inference(backward_demodulation,[],[f111,f193])).
% 1.66/0.60  fof(f111,plain,(
% 1.66/0.60    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0))) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f110,f49])).
% 1.66/0.60  fof(f110,plain,(
% 1.66/0.60    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0))) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f89,f48])).
% 1.66/0.60  fof(f48,plain,(
% 1.66/0.60    v2_pre_topc(sK0)),
% 1.66/0.60    inference(cnf_transformation,[],[f17])).
% 1.66/0.60  fof(f89,plain,(
% 1.66/0.60    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0))) )),
% 1.66/0.60    inference(resolution,[],[f47,f63])).
% 1.66/0.60  fof(f63,plain,(
% 1.66/0.60    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))) )),
% 1.66/0.60    inference(cnf_transformation,[],[f25])).
% 1.66/0.60  fof(f25,plain,(
% 1.66/0.60    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/0.60    inference(flattening,[],[f24])).
% 1.66/0.60  fof(f24,plain,(
% 1.66/0.60    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.66/0.60    inference(ennf_transformation,[],[f6])).
% 1.66/0.60  fof(f6,axiom,(
% 1.66/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_tmap_1)).
% 1.66/0.60  fof(f47,plain,(
% 1.66/0.60    ~v2_struct_0(sK0)),
% 1.66/0.60    inference(cnf_transformation,[],[f17])).
% 1.66/0.60  fof(f842,plain,(
% 1.66/0.60    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))),
% 1.66/0.60    inference(forward_demodulation,[],[f837,f580])).
% 1.66/0.60  fof(f580,plain,(
% 1.66/0.60    u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(sK0)),
% 1.66/0.60    inference(resolution,[],[f212,f197])).
% 1.66/0.60  fof(f212,plain,(
% 1.66/0.60    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | u1_struct_0(k6_tmap_1(sK0,X1)) = k2_struct_0(sK0)) )),
% 1.66/0.60    inference(forward_demodulation,[],[f200,f193])).
% 1.66/0.60  fof(f200,plain,(
% 1.66/0.60    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1))) )),
% 1.66/0.60    inference(backward_demodulation,[],[f113,f193])).
% 1.66/0.60  fof(f113,plain,(
% 1.66/0.60    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1))) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f112,f49])).
% 1.66/0.60  fof(f112,plain,(
% 1.66/0.60    ( ! [X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1))) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f90,f48])).
% 1.66/0.60  fof(f90,plain,(
% 1.66/0.60    ( ! [X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1))) )),
% 1.66/0.60    inference(resolution,[],[f47,f64])).
% 1.66/0.60  fof(f64,plain,(
% 1.66/0.60    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) )),
% 1.66/0.60    inference(cnf_transformation,[],[f27])).
% 1.66/0.60  fof(f27,plain,(
% 1.66/0.60    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/0.60    inference(flattening,[],[f26])).
% 1.66/0.60  fof(f26,plain,(
% 1.66/0.60    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.66/0.60    inference(ennf_transformation,[],[f11])).
% 1.66/0.60  fof(f11,axiom,(
% 1.66/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).
% 1.66/0.60  fof(f837,plain,(
% 1.66/0.60    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))),
% 1.66/0.60    inference(resolution,[],[f216,f197])).
% 1.66/0.60  fof(f216,plain,(
% 1.66/0.60    ( ! [X13] : (~m1_subset_1(X13,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k7_tmap_1(sK0,X13),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X13)))))) )),
% 1.66/0.60    inference(forward_demodulation,[],[f208,f193])).
% 1.66/0.60  fof(f208,plain,(
% 1.66/0.60    ( ! [X13] : (~m1_subset_1(X13,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k7_tmap_1(sK0,X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X13)))))) )),
% 1.66/0.60    inference(backward_demodulation,[],[f129,f193])).
% 1.66/0.60  fof(f129,plain,(
% 1.66/0.60    ( ! [X13] : (~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k7_tmap_1(sK0,X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X13)))))) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f128,f49])).
% 1.66/0.60  fof(f128,plain,(
% 1.66/0.60    ( ! [X13] : (~l1_pre_topc(sK0) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k7_tmap_1(sK0,X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X13)))))) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f102,f48])).
% 1.66/0.60  fof(f102,plain,(
% 1.66/0.60    ( ! [X13] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X13,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k7_tmap_1(sK0,X13),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X13)))))) )),
% 1.66/0.60    inference(resolution,[],[f47,f80])).
% 1.66/0.60  fof(f80,plain,(
% 1.66/0.60    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))) )),
% 1.66/0.60    inference(cnf_transformation,[],[f40])).
% 1.66/0.60  fof(f40,plain,(
% 1.66/0.60    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/0.60    inference(flattening,[],[f39])).
% 1.66/0.60  fof(f39,plain,(
% 1.66/0.60    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.66/0.60    inference(ennf_transformation,[],[f8])).
% 1.66/0.60  fof(f8,axiom,(
% 1.66/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 1.66/0.60  fof(f3242,plain,(
% 1.66/0.60    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.66/0.60    inference(forward_demodulation,[],[f3241,f580])).
% 1.66/0.60  fof(f3241,plain,(
% 1.66/0.60    k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))),
% 1.66/0.60    inference(subsumption_resolution,[],[f3240,f786])).
% 1.66/0.60  fof(f3240,plain,(
% 1.66/0.60    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))),
% 1.66/0.60    inference(forward_demodulation,[],[f3239,f580])).
% 1.66/0.60  fof(f3239,plain,(
% 1.66/0.60    k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))),
% 1.66/0.60    inference(subsumption_resolution,[],[f3238,f1264])).
% 1.66/0.60  fof(f1264,plain,(
% 1.66/0.60    ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.66/0.60    inference(subsumption_resolution,[],[f1263,f786])).
% 1.66/0.60  fof(f1263,plain,(
% 1.66/0.60    k1_xboole_0 = k2_struct_0(sK0) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))),
% 1.66/0.60    inference(subsumption_resolution,[],[f1252,f843])).
% 1.66/0.60  fof(f1252,plain,(
% 1.66/0.60    k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))),
% 1.66/0.60    inference(resolution,[],[f1251,f624])).
% 1.66/0.60  fof(f624,plain,(
% 1.66/0.60    ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))),
% 1.66/0.60    inference(forward_demodulation,[],[f623,f585])).
% 1.66/0.60  fof(f585,plain,(
% 1.66/0.60    k2_struct_0(sK0) = k2_struct_0(k6_tmap_1(sK0,sK1))),
% 1.66/0.60    inference(backward_demodulation,[],[f412,f580])).
% 1.66/0.60  fof(f412,plain,(
% 1.66/0.60    u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(k6_tmap_1(sK0,sK1))),
% 1.66/0.60    inference(resolution,[],[f373,f50])).
% 1.66/0.60  fof(f373,plain,(
% 1.66/0.60    l1_struct_0(k6_tmap_1(sK0,sK1))),
% 1.66/0.60    inference(resolution,[],[f368,f51])).
% 1.66/0.60  fof(f368,plain,(
% 1.66/0.60    l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 1.66/0.60    inference(resolution,[],[f205,f197])).
% 1.66/0.60  fof(f205,plain,(
% 1.66/0.60    ( ! [X10] : (~m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0))) | l1_pre_topc(k6_tmap_1(sK0,X10))) )),
% 1.66/0.60    inference(backward_demodulation,[],[f123,f193])).
% 1.66/0.60  fof(f123,plain,(
% 1.66/0.60    ( ! [X10] : (~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | l1_pre_topc(k6_tmap_1(sK0,X10))) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f122,f49])).
% 1.66/0.60  fof(f122,plain,(
% 1.66/0.60    ( ! [X10] : (~l1_pre_topc(sK0) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | l1_pre_topc(k6_tmap_1(sK0,X10))) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f99,f48])).
% 1.66/0.60  fof(f99,plain,(
% 1.66/0.60    ( ! [X10] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | l1_pre_topc(k6_tmap_1(sK0,X10))) )),
% 1.66/0.60    inference(resolution,[],[f47,f77])).
% 1.66/0.60  fof(f77,plain,(
% 1.66/0.60    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | l1_pre_topc(k6_tmap_1(X0,X1))) )),
% 1.66/0.60    inference(cnf_transformation,[],[f38])).
% 1.66/0.60  fof(f38,plain,(
% 1.66/0.60    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/0.60    inference(flattening,[],[f37])).
% 1.66/0.60  fof(f37,plain,(
% 1.66/0.60    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.66/0.60    inference(ennf_transformation,[],[f7])).
% 1.66/0.60  fof(f7,axiom,(
% 1.66/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 1.66/0.60  fof(f623,plain,(
% 1.66/0.60    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1))) | ~v3_pre_topc(sK1,sK0)),
% 1.66/0.60    inference(subsumption_resolution,[],[f598,f551])).
% 1.66/0.60  fof(f551,plain,(
% 1.66/0.60    v1_funct_1(k6_partfun1(k2_struct_0(sK0)))),
% 1.66/0.60    inference(backward_demodulation,[],[f417,f541])).
% 1.66/0.60  fof(f417,plain,(
% 1.66/0.60    v1_funct_1(k7_tmap_1(sK0,sK1))),
% 1.66/0.60    inference(resolution,[],[f206,f197])).
% 1.66/0.60  fof(f206,plain,(
% 1.66/0.60    ( ! [X11] : (~m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK0))) | v1_funct_1(k7_tmap_1(sK0,X11))) )),
% 1.66/0.60    inference(backward_demodulation,[],[f125,f193])).
% 1.66/0.60  fof(f125,plain,(
% 1.66/0.60    ( ! [X11] : (~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | v1_funct_1(k7_tmap_1(sK0,X11))) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f124,f49])).
% 1.66/0.60  fof(f124,plain,(
% 1.66/0.60    ( ! [X11] : (~l1_pre_topc(sK0) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | v1_funct_1(k7_tmap_1(sK0,X11))) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f100,f48])).
% 1.66/0.60  fof(f100,plain,(
% 1.66/0.60    ( ! [X11] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | v1_funct_1(k7_tmap_1(sK0,X11))) )),
% 1.66/0.60    inference(resolution,[],[f47,f78])).
% 1.66/0.60  fof(f78,plain,(
% 1.66/0.60    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_1(k7_tmap_1(X0,X1))) )),
% 1.66/0.60    inference(cnf_transformation,[],[f40])).
% 1.66/0.60  fof(f598,plain,(
% 1.66/0.60    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0)),
% 1.66/0.60    inference(backward_demodulation,[],[f554,f585])).
% 1.66/0.60  fof(f554,plain,(
% 1.66/0.60    ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0)),
% 1.66/0.60    inference(forward_demodulation,[],[f553,f541])).
% 1.66/0.60  fof(f553,plain,(
% 1.66/0.60    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 1.66/0.60    inference(forward_demodulation,[],[f552,f541])).
% 1.66/0.60  fof(f552,plain,(
% 1.66/0.60    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1))) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 1.66/0.60    inference(forward_demodulation,[],[f550,f541])).
% 1.66/0.60  fof(f550,plain,(
% 1.66/0.60    ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1))) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 1.66/0.60    inference(backward_demodulation,[],[f416,f541])).
% 1.66/0.60  fof(f416,plain,(
% 1.66/0.60    ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 1.66/0.60    inference(forward_demodulation,[],[f415,f412])).
% 1.66/0.60  fof(f415,plain,(
% 1.66/0.60    ~v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 1.66/0.60    inference(backward_demodulation,[],[f210,f412])).
% 1.66/0.60  fof(f210,plain,(
% 1.66/0.60    ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 1.66/0.60    inference(forward_demodulation,[],[f194,f193])).
% 1.66/0.60  fof(f194,plain,(
% 1.66/0.60    ~v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v3_pre_topc(sK1,sK0)),
% 1.66/0.60    inference(backward_demodulation,[],[f41,f193])).
% 1.66/0.60  fof(f41,plain,(
% 1.66/0.60    ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v3_pre_topc(sK1,sK0)),
% 1.66/0.60    inference(cnf_transformation,[],[f17])).
% 1.66/0.60  fof(f1251,plain,(
% 1.66/0.60    v3_pre_topc(sK1,sK0) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.66/0.60    inference(subsumption_resolution,[],[f1250,f800])).
% 1.66/0.60  fof(f800,plain,(
% 1.66/0.60    k6_tmap_1(sK0,sK1) != g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) | v3_pre_topc(sK1,sK0)),
% 1.66/0.60    inference(resolution,[],[f213,f197])).
% 1.66/0.60  fof(f213,plain,(
% 1.66/0.60    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | k6_tmap_1(sK0,X3) != g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) | v3_pre_topc(X3,sK0)) )),
% 1.66/0.60    inference(forward_demodulation,[],[f202,f193])).
% 1.66/0.60  fof(f202,plain,(
% 1.66/0.60    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X3) | v3_pre_topc(X3,sK0)) )),
% 1.66/0.60    inference(backward_demodulation,[],[f117,f193])).
% 1.66/0.60  fof(f117,plain,(
% 1.66/0.60    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X3) | v3_pre_topc(X3,sK0)) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f116,f49])).
% 1.66/0.60  fof(f116,plain,(
% 1.66/0.60    ( ! [X3] : (~l1_pre_topc(sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X3) | v3_pre_topc(X3,sK0)) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f92,f48])).
% 1.66/0.60  fof(f92,plain,(
% 1.66/0.60    ( ! [X3] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) != k6_tmap_1(sK0,X3) | v3_pre_topc(X3,sK0)) )),
% 1.66/0.60    inference(resolution,[],[f47,f66])).
% 1.66/0.60  fof(f66,plain,(
% 1.66/0.60    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) != k6_tmap_1(X0,X1) | v3_pre_topc(X1,X0)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f29])).
% 1.66/0.60  fof(f29,plain,(
% 1.66/0.60    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/0.60    inference(flattening,[],[f28])).
% 1.66/0.60  fof(f28,plain,(
% 1.66/0.60    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.66/0.60    inference(ennf_transformation,[],[f13])).
% 1.66/0.60  fof(f13,axiom,(
% 1.66/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_tmap_1)).
% 1.66/0.60  fof(f1250,plain,(
% 1.66/0.60    v3_pre_topc(sK1,sK0) | k1_xboole_0 = k2_struct_0(sK0) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),
% 1.66/0.60    inference(forward_demodulation,[],[f1249,f227])).
% 1.66/0.60  fof(f227,plain,(
% 1.66/0.60    sK1 = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1)),
% 1.66/0.60    inference(resolution,[],[f197,f71])).
% 1.66/0.60  fof(f71,plain,(
% 1.66/0.60    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1) )),
% 1.66/0.60    inference(cnf_transformation,[],[f34])).
% 1.66/0.60  fof(f34,plain,(
% 1.66/0.60    ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.66/0.60    inference(ennf_transformation,[],[f1])).
% 1.66/0.60  fof(f1,axiom,(
% 1.66/0.60    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).
% 1.66/0.60  fof(f1249,plain,(
% 1.66/0.60    k1_xboole_0 = k2_struct_0(sK0) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1),sK0) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),
% 1.66/0.60    inference(subsumption_resolution,[],[f1248,f551])).
% 1.66/0.60  fof(f1248,plain,(
% 1.66/0.60    k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1),sK0) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),
% 1.66/0.60    inference(subsumption_resolution,[],[f1247,f786])).
% 1.66/0.60  fof(f1247,plain,(
% 1.66/0.60    k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1),sK0) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),
% 1.66/0.60    inference(subsumption_resolution,[],[f1233,f843])).
% 1.66/0.60  fof(f1233,plain,(
% 1.66/0.60    k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1),sK0) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),
% 1.66/0.60    inference(resolution,[],[f1224,f830])).
% 1.66/0.60  fof(f830,plain,(
% 1.66/0.60    v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),
% 1.66/0.60    inference(subsumption_resolution,[],[f814,f197])).
% 1.66/0.60  fof(f814,plain,(
% 1.66/0.60    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))),
% 1.66/0.60    inference(resolution,[],[f214,f547])).
% 1.66/0.60  fof(f547,plain,(
% 1.66/0.60    v3_pre_topc(sK1,sK0) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))),
% 1.66/0.60    inference(backward_demodulation,[],[f44,f541])).
% 1.66/0.60  fof(f44,plain,(
% 1.66/0.60    v3_pre_topc(sK1,sK0) | v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))),
% 1.66/0.60    inference(cnf_transformation,[],[f17])).
% 1.66/0.60  fof(f214,plain,(
% 1.66/0.60    ( ! [X4] : (~v3_pre_topc(X4,sK0) | ~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | k6_tmap_1(sK0,X4) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) )),
% 1.66/0.60    inference(forward_demodulation,[],[f203,f193])).
% 1.66/0.60  fof(f203,plain,(
% 1.66/0.60    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X4) | ~v3_pre_topc(X4,sK0)) )),
% 1.66/0.60    inference(backward_demodulation,[],[f119,f193])).
% 1.66/0.60  fof(f119,plain,(
% 1.66/0.60    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X4) | ~v3_pre_topc(X4,sK0)) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f118,f49])).
% 1.66/0.60  fof(f118,plain,(
% 1.66/0.60    ( ! [X4] : (~l1_pre_topc(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X4) | ~v3_pre_topc(X4,sK0)) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f93,f48])).
% 1.66/0.60  fof(f93,plain,(
% 1.66/0.60    ( ! [X4] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | g1_pre_topc(u1_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X4) | ~v3_pre_topc(X4,sK0)) )),
% 1.66/0.60    inference(resolution,[],[f47,f67])).
% 1.66/0.60  fof(f67,plain,(
% 1.66/0.60    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f29])).
% 1.66/0.60  fof(f1224,plain,(
% 1.66/0.60    ( ! [X20] : (~v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(X20,k2_struct_0(sK0),k2_struct_0(sK0)) | ~v1_funct_1(X20) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X20,sK1),sK0)) )),
% 1.66/0.60    inference(forward_demodulation,[],[f1223,f580])).
% 1.66/0.60  fof(f1223,plain,(
% 1.66/0.60    ( ! [X20] : (k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(X20,k2_struct_0(sK0),k2_struct_0(sK0)) | ~v1_funct_1(X20) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),sK0) | ~v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f1222,f197])).
% 1.66/0.60  fof(f1222,plain,(
% 1.66/0.60    ( ! [X20] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(X20,k2_struct_0(sK0),k2_struct_0(sK0)) | ~v1_funct_1(X20) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),sK0) | ~v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.60    inference(forward_demodulation,[],[f1221,f580])).
% 1.66/0.60  fof(f1221,plain,(
% 1.66/0.60    ( ! [X20] : (k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(X20,k2_struct_0(sK0),k2_struct_0(sK0)) | ~v1_funct_1(X20) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),sK0) | ~v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.60    inference(forward_demodulation,[],[f1220,f585])).
% 1.66/0.60  fof(f1220,plain,(
% 1.66/0.60    ( ! [X20] : (~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(X20,k2_struct_0(sK0),k2_struct_0(sK0)) | ~v1_funct_1(X20) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),sK0) | ~v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.60    inference(forward_demodulation,[],[f1219,f580])).
% 1.66/0.60  fof(f1219,plain,(
% 1.66/0.60    ( ! [X20] : (~v1_funct_2(X20,k2_struct_0(sK0),k2_struct_0(sK0)) | ~v1_funct_1(X20) | ~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),sK0) | ~v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.60    inference(forward_demodulation,[],[f1218,f580])).
% 1.66/0.60  fof(f1218,plain,(
% 1.66/0.60    ( ! [X20] : (~v1_funct_1(X20) | ~v1_funct_2(X20,k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),sK0) | ~v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f1205,f368])).
% 1.66/0.60  fof(f1205,plain,(
% 1.66/0.60    ( ! [X20] : (~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X20) | ~v1_funct_2(X20,k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),sK0) | ~v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.60    inference(resolution,[],[f317,f796])).
% 1.66/0.60  fof(f796,plain,(
% 1.66/0.60    v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))),
% 1.66/0.60    inference(subsumption_resolution,[],[f795,f197])).
% 1.66/0.60  fof(f795,plain,(
% 1.66/0.60    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))),
% 1.66/0.60    inference(duplicate_literal_removal,[],[f792])).
% 1.66/0.60  fof(f792,plain,(
% 1.66/0.60    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))),
% 1.66/0.60    inference(superposition,[],[f209,f580])).
% 1.66/0.60  fof(f209,plain,(
% 1.66/0.60    ( ! [X14] : (~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X14)))) | ~m1_subset_1(X14,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(X14,k6_tmap_1(sK0,X14))) )),
% 1.66/0.60    inference(backward_demodulation,[],[f131,f193])).
% 1.66/0.60  fof(f131,plain,(
% 1.66/0.60    ( ! [X14] : (~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X14)))) | v3_pre_topc(X14,k6_tmap_1(sK0,X14))) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f130,f49])).
% 1.66/0.60  fof(f130,plain,(
% 1.66/0.60    ( ! [X14] : (~l1_pre_topc(sK0) | ~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X14)))) | v3_pre_topc(X14,k6_tmap_1(sK0,X14))) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f103,f48])).
% 1.66/0.60  fof(f103,plain,(
% 1.66/0.60    ( ! [X14] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X14,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X14)))) | v3_pre_topc(X14,k6_tmap_1(sK0,X14))) )),
% 1.66/0.60    inference(resolution,[],[f47,f81])).
% 1.66/0.60  fof(f81,plain,(
% 1.66/0.60    ( ! [X2,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2)))) | v3_pre_topc(X2,k6_tmap_1(X0,X2))) )),
% 1.66/0.60    inference(equality_resolution,[],[f68])).
% 1.66/0.60  fof(f68,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) | X1 != X2 | v3_pre_topc(X2,k6_tmap_1(X0,X1))) )),
% 1.66/0.60    inference(cnf_transformation,[],[f31])).
% 1.66/0.60  fof(f31,plain,(
% 1.66/0.60    ! [X0] : (! [X1] : (! [X2] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/0.60    inference(flattening,[],[f30])).
% 1.66/0.60  fof(f30,plain,(
% 1.66/0.60    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.66/0.60    inference(ennf_transformation,[],[f12])).
% 1.66/0.60  fof(f12,axiom,(
% 1.66/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) => (X1 = X2 => v3_pre_topc(X2,k6_tmap_1(X0,X1))))))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tmap_1)).
% 1.66/0.60  fof(f317,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (~v3_pre_topc(X2,X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | k2_struct_0(X0) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X0),X1,X2),sK0) | ~v5_pre_topc(X1,sK0,X0)) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f235,f49])).
% 1.66/0.60  fof(f235,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X0),X1,X2),sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X0)))) | k2_struct_0(X0) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~v3_pre_topc(X2,X0) | ~v5_pre_topc(X1,sK0,X0)) )),
% 1.66/0.60    inference(superposition,[],[f52,f193])).
% 1.66/0.60  fof(f52,plain,(
% 1.66/0.60    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1) | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v5_pre_topc(X2,X0,X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f21])).
% 1.66/0.60  fof(f21,plain,(
% 1.66/0.60    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.66/0.60    inference(flattening,[],[f20])).
% 1.66/0.60  fof(f20,plain,(
% 1.66/0.60    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.66/0.60    inference(ennf_transformation,[],[f5])).
% 1.66/0.60  fof(f5,axiom,(
% 1.66/0.60    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_struct_0(X1) = k1_xboole_0 => k2_struct_0(X0) = k1_xboole_0) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_2)).
% 1.66/0.60  fof(f3238,plain,(
% 1.66/0.60    k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))),
% 1.66/0.60    inference(subsumption_resolution,[],[f3237,f551])).
% 1.66/0.60  fof(f3237,plain,(
% 1.66/0.60    k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))),
% 1.66/0.60    inference(subsumption_resolution,[],[f3236,f368])).
% 1.66/0.60  fof(f3236,plain,(
% 1.66/0.60    k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))),
% 1.66/0.60    inference(subsumption_resolution,[],[f3235,f341])).
% 1.66/0.60  fof(f341,plain,(
% 1.66/0.60    v2_pre_topc(k6_tmap_1(sK0,sK1))),
% 1.66/0.60    inference(resolution,[],[f204,f197])).
% 1.66/0.60  fof(f204,plain,(
% 1.66/0.60    ( ! [X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) | v2_pre_topc(k6_tmap_1(sK0,X7))) )),
% 1.66/0.60    inference(backward_demodulation,[],[f121,f193])).
% 1.66/0.60  fof(f121,plain,(
% 1.66/0.60    ( ! [X7] : (~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | v2_pre_topc(k6_tmap_1(sK0,X7))) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f120,f49])).
% 1.66/0.60  fof(f120,plain,(
% 1.66/0.60    ( ! [X7] : (~l1_pre_topc(sK0) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | v2_pre_topc(k6_tmap_1(sK0,X7))) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f96,f48])).
% 1.66/0.60  fof(f96,plain,(
% 1.66/0.60    ( ! [X7] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | v2_pre_topc(k6_tmap_1(sK0,X7))) )),
% 1.66/0.60    inference(resolution,[],[f47,f74])).
% 1.66/0.60  fof(f74,plain,(
% 1.66/0.60    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v2_pre_topc(k6_tmap_1(X0,X1))) )),
% 1.66/0.60    inference(cnf_transformation,[],[f36])).
% 1.66/0.60  fof(f36,plain,(
% 1.66/0.60    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.66/0.60    inference(flattening,[],[f35])).
% 1.66/0.60  fof(f35,plain,(
% 1.66/0.60    ! [X0,X1] : ((v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.66/0.60    inference(ennf_transformation,[],[f10])).
% 1.66/0.60  fof(f10,axiom,(
% 1.66/0.60    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1)) & ~v2_struct_0(k6_tmap_1(X0,X1))))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_tmap_1)).
% 1.66/0.60  fof(f3235,plain,(
% 1.66/0.60    k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))),
% 1.66/0.60    inference(duplicate_literal_removal,[],[f3227])).
% 1.66/0.60  fof(f3227,plain,(
% 1.66/0.60    k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.66/0.60    inference(resolution,[],[f3225,f2404])).
% 1.66/0.60  fof(f2404,plain,(
% 1.66/0.60    ( ! [X0,X1] : (~v5_pre_topc(X0,k6_tmap_1(sK0,sK1),X1) | ~v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | v5_pre_topc(X0,sK0,X1) | k1_xboole_0 = k2_struct_0(sK0)) )),
% 1.66/0.60    inference(duplicate_literal_removal,[],[f2403])).
% 1.66/0.60  fof(f2403,plain,(
% 1.66/0.60    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1)) | ~v5_pre_topc(X0,k6_tmap_1(sK0,sK1),X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1)))) | v5_pre_topc(X0,sK0,X1) | k1_xboole_0 = k2_struct_0(sK0)) )),
% 1.66/0.60    inference(forward_demodulation,[],[f2402,f580])).
% 1.66/0.60  fof(f2402,plain,(
% 1.66/0.60    ( ! [X0,X1] : (~v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1)) | ~v5_pre_topc(X0,k6_tmap_1(sK0,sK1),X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X1)))) | v5_pre_topc(X0,sK0,X1) | k1_xboole_0 = k2_struct_0(sK0)) )),
% 1.66/0.60    inference(duplicate_literal_removal,[],[f2401])).
% 1.66/0.60  fof(f2401,plain,(
% 1.66/0.60    ( ! [X0,X1] : (~v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1)) | ~v5_pre_topc(X0,k6_tmap_1(sK0,sK1),X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1)))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X1)))) | v5_pre_topc(X0,sK0,X1) | k1_xboole_0 = k2_struct_0(sK0)) )),
% 1.66/0.60    inference(forward_demodulation,[],[f2398,f580])).
% 1.66/0.60  fof(f2398,plain,(
% 1.66/0.60    ( ! [X0,X1] : (~v5_pre_topc(X0,k6_tmap_1(sK0,sK1),X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X1)))) | v5_pre_topc(X0,sK0,X1) | k1_xboole_0 = k2_struct_0(sK0)) )),
% 1.66/0.60    inference(superposition,[],[f330,f1265])).
% 1.66/0.60  fof(f1265,plain,(
% 1.66/0.60    k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.66/0.60    inference(subsumption_resolution,[],[f1253,f197])).
% 1.66/0.60  fof(f1253,plain,(
% 1.66/0.60    k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),
% 1.66/0.60    inference(resolution,[],[f1251,f214])).
% 1.66/0.60  fof(f330,plain,(
% 1.66/0.60    ( ! [X142,X141] : (~v5_pre_topc(X141,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X142) | ~v2_pre_topc(X142) | ~l1_pre_topc(X142) | ~v1_funct_1(X141) | ~v1_funct_2(X141,k2_struct_0(sK0),u1_struct_0(X142)) | ~m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X142)))) | ~v1_funct_2(X141,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X142)) | ~m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X142)))) | v5_pre_topc(X141,sK0,X142)) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f329,f49])).
% 1.66/0.60  fof(f329,plain,(
% 1.66/0.60    ( ! [X142,X141] : (~v5_pre_topc(X141,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X142) | ~l1_pre_topc(sK0) | ~v2_pre_topc(X142) | ~l1_pre_topc(X142) | ~v1_funct_1(X141) | ~v1_funct_2(X141,k2_struct_0(sK0),u1_struct_0(X142)) | ~m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X142)))) | ~v1_funct_2(X141,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X142)) | ~m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X142)))) | v5_pre_topc(X141,sK0,X142)) )),
% 1.66/0.60    inference(subsumption_resolution,[],[f312,f48])).
% 1.66/0.60  fof(f312,plain,(
% 1.66/0.60    ( ! [X142,X141] : (~v5_pre_topc(X141,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X142) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v2_pre_topc(X142) | ~l1_pre_topc(X142) | ~v1_funct_1(X141) | ~v1_funct_2(X141,k2_struct_0(sK0),u1_struct_0(X142)) | ~m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X142)))) | ~v1_funct_2(X141,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X142)) | ~m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X142)))) | v5_pre_topc(X141,sK0,X142)) )),
% 1.66/0.60    inference(superposition,[],[f85,f193])).
% 1.66/0.60  fof(f85,plain,(
% 1.66/0.60    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1)) )),
% 1.66/0.60    inference(duplicate_literal_removal,[],[f83])).
% 1.66/0.60  fof(f83,plain,(
% 1.66/0.60    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1)) )),
% 1.66/0.60    inference(equality_resolution,[],[f69])).
% 1.66/0.60  fof(f69,plain,(
% 1.66/0.60    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | X2 != X3 | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f33])).
% 1.66/0.60  fof(f33,plain,(
% 1.66/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 1.66/0.60    inference(flattening,[],[f32])).
% 1.66/0.60  fof(f32,plain,(
% 1.66/0.60    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 1.66/0.60    inference(ennf_transformation,[],[f4])).
% 1.66/0.60  fof(f4,axiom,(
% 1.66/0.60    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 1.66/0.60    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_pre_topc)).
% 1.66/0.60  fof(f3225,plain,(
% 1.66/0.60    v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.66/0.60    inference(duplicate_literal_removal,[],[f3224])).
% 1.66/0.60  fof(f3224,plain,(
% 1.66/0.60    k1_xboole_0 = k2_struct_0(sK0) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.66/0.60    inference(forward_demodulation,[],[f3223,f585])).
% 1.66/0.60  fof(f3223,plain,(
% 1.66/0.60    v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))),
% 1.66/0.60    inference(subsumption_resolution,[],[f3222,f843])).
% 1.66/0.60  fof(f3222,plain,(
% 1.66/0.60    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))),
% 1.66/0.60    inference(forward_demodulation,[],[f3221,f580])).
% 1.66/0.60  fof(f3221,plain,(
% 1.66/0.60    v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))),
% 1.66/0.60    inference(subsumption_resolution,[],[f3220,f786])).
% 1.66/0.60  fof(f3220,plain,(
% 1.66/0.60    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))),
% 1.66/0.60    inference(forward_demodulation,[],[f3219,f580])).
% 1.66/0.60  fof(f3219,plain,(
% 1.66/0.60    v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))),
% 1.66/0.60    inference(subsumption_resolution,[],[f3218,f551])).
% 1.66/0.60  fof(f3218,plain,(
% 1.66/0.60    v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))),
% 1.66/0.60    inference(subsumption_resolution,[],[f3217,f368])).
% 1.66/0.60  fof(f3217,plain,(
% 1.66/0.60    v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))),
% 1.66/0.60    inference(duplicate_literal_removal,[],[f3209])).
% 1.66/0.60  fof(f3209,plain,(
% 1.66/0.60    v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))),
% 1.66/0.60    inference(resolution,[],[f3208,f54])).
% 1.66/0.60  fof(f54,plain,(
% 1.66/0.60    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X1) = k1_xboole_0 | v3_pre_topc(sK2(X0,X1,X2),X1) | v5_pre_topc(X2,X0,X1)) )),
% 1.66/0.60    inference(cnf_transformation,[],[f21])).
% 1.66/0.60  fof(f3208,plain,(
% 1.66/0.60    ~v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.66/0.60    inference(subsumption_resolution,[],[f3207,f551])).
% 1.66/0.60  fof(f3207,plain,(
% 1.66/0.60    ~v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.66/0.60    inference(subsumption_resolution,[],[f3206,f843])).
% 1.66/0.60  fof(f3206,plain,(
% 1.66/0.60    ~v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.66/0.60    inference(subsumption_resolution,[],[f3205,f786])).
% 1.66/0.61  fof(f3205,plain,(
% 1.66/0.61    ~v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.66/0.61    inference(superposition,[],[f1182,f2615])).
% 1.66/0.61  fof(f2615,plain,(
% 1.66/0.61    sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.66/0.61    inference(resolution,[],[f2567,f71])).
% 1.66/0.61  fof(f2567,plain,(
% 1.66/0.61    m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.66/0.61    inference(subsumption_resolution,[],[f2566,f1264])).
% 1.66/0.61  fof(f2566,plain,(
% 1.66/0.61    k1_xboole_0 = k2_struct_0(sK0) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.66/0.61    inference(subsumption_resolution,[],[f2565,f551])).
% 1.66/0.61  fof(f2565,plain,(
% 1.66/0.61    k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.66/0.61    inference(subsumption_resolution,[],[f2557,f843])).
% 1.66/0.61  fof(f2557,plain,(
% 1.66/0.61    k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.66/0.61    inference(resolution,[],[f2454,f786])).
% 1.66/0.61  fof(f2454,plain,(
% 1.66/0.61    ( ! [X5] : (~v1_funct_2(X5,k2_struct_0(sK0),k2_struct_0(sK0)) | k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_1(X5) | v5_pre_topc(X5,sK0,k6_tmap_1(sK0,sK1)) | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5),k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.66/0.61    inference(duplicate_literal_removal,[],[f2453])).
% 1.66/0.61  fof(f2453,plain,(
% 1.66/0.61    ( ! [X5] : (k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_2(X5,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_1(X5) | v5_pre_topc(X5,sK0,k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(sK0) | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5),k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f2452,f585])).
% 1.66/0.61  fof(f2452,plain,(
% 1.66/0.61    ( ! [X5] : (~v1_funct_2(X5,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_1(X5) | v5_pre_topc(X5,sK0,k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5),k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f2451,f368])).
% 1.66/0.61  fof(f2451,plain,(
% 1.66/0.61    ( ! [X5] : (~v1_funct_2(X5,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X5) | v5_pre_topc(X5,sK0,k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5),k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f2434,f341])).
% 1.66/0.61  fof(f2434,plain,(
% 1.66/0.61    ( ! [X5] : (~v1_funct_2(X5,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X5) | v5_pre_topc(X5,sK0,k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5),k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.66/0.61    inference(superposition,[],[f2419,f580])).
% 1.66/0.61  fof(f2419,plain,(
% 1.66/0.61    ( ! [X0,X1] : (~v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | v5_pre_topc(X0,sK0,X1) | k1_xboole_0 = k2_struct_0(sK0) | k2_struct_0(X1) = k1_xboole_0 | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),X1,X0),k1_zfmisc_1(u1_struct_0(X1)))) )),
% 1.66/0.61    inference(duplicate_literal_removal,[],[f2418])).
% 1.66/0.61  fof(f2418,plain,(
% 1.66/0.61    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | v5_pre_topc(X0,sK0,X1) | k1_xboole_0 = k2_struct_0(sK0) | k2_struct_0(X1) = k1_xboole_0 | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),X1,X0),k1_zfmisc_1(u1_struct_0(X1)))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f2417,f580])).
% 1.66/0.61  fof(f2417,plain,(
% 1.66/0.61    ( ! [X0,X1] : (~v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | v5_pre_topc(X0,sK0,X1) | k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X1)))) | k2_struct_0(X1) = k1_xboole_0 | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),X1,X0),k1_zfmisc_1(u1_struct_0(X1)))) )),
% 1.66/0.61    inference(duplicate_literal_removal,[],[f2416])).
% 1.66/0.61  fof(f2416,plain,(
% 1.66/0.61    ( ! [X0,X1] : (~v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | v5_pre_topc(X0,sK0,X1) | k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X1)))) | k2_struct_0(X1) = k1_xboole_0 | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),X1,X0),k1_zfmisc_1(u1_struct_0(X1)))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f2415,f580])).
% 1.66/0.61  fof(f2415,plain,(
% 1.66/0.61    ( ! [X0,X1] : (~v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | v5_pre_topc(X0,sK0,X1) | k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_2(X0,u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X1)))) | k2_struct_0(X1) = k1_xboole_0 | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),X1,X0),k1_zfmisc_1(u1_struct_0(X1)))) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f2414,f368])).
% 1.66/0.61  fof(f2414,plain,(
% 1.66/0.61    ( ! [X0,X1] : (~v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | v5_pre_topc(X0,sK0,X1) | k1_xboole_0 = k2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_2(X0,u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X1)))) | k2_struct_0(X1) = k1_xboole_0 | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),X1,X0),k1_zfmisc_1(u1_struct_0(X1)))) )),
% 1.66/0.61    inference(duplicate_literal_removal,[],[f2405])).
% 1.66/0.61  fof(f2405,plain,(
% 1.66/0.61    ( ! [X0,X1] : (~v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | v5_pre_topc(X0,sK0,X1) | k1_xboole_0 = k2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X1)))) | k2_struct_0(X1) = k1_xboole_0 | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),X1,X0),k1_zfmisc_1(u1_struct_0(X1)))) )),
% 1.66/0.61    inference(resolution,[],[f2404,f53])).
% 1.66/0.61  fof(f53,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X1) = k1_xboole_0 | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | v5_pre_topc(X2,X0,X1)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f21])).
% 1.66/0.61  fof(f1182,plain,(
% 1.66/0.61    ( ! [X5] : (~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X5,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5)),k6_tmap_1(sK0,sK1)) | ~v1_funct_2(X5,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_1(X5) | v5_pre_topc(X5,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f1181,f1170])).
% 1.66/0.61  fof(f1170,plain,(
% 1.66/0.61    ( ! [X5] : (~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X5,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5)),k6_tmap_1(sK0,sK1)) | ~v1_funct_2(X5,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_1(X5) | v5_pre_topc(X5,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f1164,f368])).
% 1.66/0.61  fof(f1164,plain,(
% 1.66/0.61    ( ! [X5] : (~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X5,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5)),k6_tmap_1(sK0,sK1)) | ~v1_funct_2(X5,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | k1_xboole_0 = k2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X5) | v5_pre_topc(X5,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(superposition,[],[f609,f580])).
% 1.66/0.61  fof(f609,plain,(
% 1.66/0.61    ( ! [X47,X46] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X46),k2_struct_0(sK0),X47,sK2(X46,k6_tmap_1(sK0,sK1),X47)),X46) | ~v1_funct_2(X47,u1_struct_0(X46),k2_struct_0(sK0)) | ~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),k2_struct_0(sK0)))) | k1_xboole_0 = k2_struct_0(sK0) | ~l1_pre_topc(X46) | ~v1_funct_1(X47) | v5_pre_topc(X47,X46,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f608,f585])).
% 1.66/0.61  fof(f608,plain,(
% 1.66/0.61    ( ! [X47,X46] : (~v1_funct_2(X47,u1_struct_0(X46),k2_struct_0(sK0)) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X46),k2_struct_0(sK0),X47,sK2(X46,k6_tmap_1(sK0,sK1),X47)),X46) | k1_xboole_0 = k2_struct_0(sK0) | ~l1_pre_topc(X46) | ~v1_funct_1(X47) | ~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),k2_struct_0(k6_tmap_1(sK0,sK1))))) | v5_pre_topc(X47,X46,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f607,f585])).
% 1.66/0.61  fof(f607,plain,(
% 1.66/0.61    ( ! [X47,X46] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X46),k2_struct_0(sK0),X47,sK2(X46,k6_tmap_1(sK0,sK1),X47)),X46) | k1_xboole_0 = k2_struct_0(sK0) | ~l1_pre_topc(X46) | ~v1_funct_1(X47) | ~v1_funct_2(X47,u1_struct_0(X46),k2_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),k2_struct_0(k6_tmap_1(sK0,sK1))))) | v5_pre_topc(X47,X46,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f589,f585])).
% 1.66/0.61  fof(f589,plain,(
% 1.66/0.61    ( ! [X47,X46] : (k1_xboole_0 = k2_struct_0(sK0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X46),k2_struct_0(k6_tmap_1(sK0,sK1)),X47,sK2(X46,k6_tmap_1(sK0,sK1),X47)),X46) | ~l1_pre_topc(X46) | ~v1_funct_1(X47) | ~v1_funct_2(X47,u1_struct_0(X46),k2_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),k2_struct_0(k6_tmap_1(sK0,sK1))))) | v5_pre_topc(X47,X46,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(backward_demodulation,[],[f526,f585])).
% 1.66/0.61  fof(f526,plain,(
% 1.66/0.61    ( ! [X47,X46] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X46),k2_struct_0(k6_tmap_1(sK0,sK1)),X47,sK2(X46,k6_tmap_1(sK0,sK1),X47)),X46) | ~l1_pre_topc(X46) | ~v1_funct_1(X47) | ~v1_funct_2(X47,u1_struct_0(X46),k2_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),k2_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | v5_pre_topc(X47,X46,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f462,f368])).
% 1.66/0.61  fof(f462,plain,(
% 1.66/0.61    ( ! [X47,X46] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X46),k2_struct_0(k6_tmap_1(sK0,sK1)),X47,sK2(X46,k6_tmap_1(sK0,sK1),X47)),X46) | ~l1_pre_topc(X46) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X47) | ~v1_funct_2(X47,u1_struct_0(X46),k2_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(X47,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X46),k2_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | v5_pre_topc(X47,X46,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(superposition,[],[f55,f412])).
% 1.66/0.61  fof(f55,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X1) = k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) | v5_pre_topc(X2,X0,X1)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f21])).
% 1.66/0.61  fof(f1181,plain,(
% 1.66/0.61    ( ! [X5] : (k1_xboole_0 != k2_struct_0(sK0) | ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X5,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5)),k6_tmap_1(sK0,sK1)) | ~v1_funct_2(X5,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_1(X5) | v5_pre_topc(X5,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f1180,f585])).
% 1.66/0.61  fof(f1180,plain,(
% 1.66/0.61    ( ! [X5] : (~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X5,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5)),k6_tmap_1(sK0,sK1)) | ~v1_funct_2(X5,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_1(X5) | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1)) | v5_pre_topc(X5,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f1174,f368])).
% 1.66/0.61  fof(f1174,plain,(
% 1.66/0.61    ( ! [X5] : (~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X5,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5)),k6_tmap_1(sK0,sK1)) | ~v1_funct_2(X5,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X5) | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1)) | v5_pre_topc(X5,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(superposition,[],[f614,f580])).
% 1.66/0.61  fof(f614,plain,(
% 1.66/0.61    ( ! [X94,X95] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X94),k2_struct_0(sK0),X95,sK2(X94,k6_tmap_1(sK0,sK1),X95)),X94) | ~v1_funct_2(X95,u1_struct_0(X94),k2_struct_0(sK0)) | ~m1_subset_1(X95,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X94),k2_struct_0(sK0)))) | ~l1_pre_topc(X94) | ~v1_funct_1(X95) | k1_xboole_0 != k2_struct_0(X94) | v5_pre_topc(X95,X94,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f613,f585])).
% 1.66/0.61  fof(f613,plain,(
% 1.66/0.61    ( ! [X94,X95] : (~v1_funct_2(X95,u1_struct_0(X94),k2_struct_0(sK0)) | ~v3_pre_topc(k8_relset_1(u1_struct_0(X94),k2_struct_0(sK0),X95,sK2(X94,k6_tmap_1(sK0,sK1),X95)),X94) | ~l1_pre_topc(X94) | ~v1_funct_1(X95) | ~m1_subset_1(X95,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X94),k2_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(X94) | v5_pre_topc(X95,X94,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f593,f585])).
% 1.66/0.61  fof(f593,plain,(
% 1.66/0.61    ( ! [X94,X95] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X94),k2_struct_0(sK0),X95,sK2(X94,k6_tmap_1(sK0,sK1),X95)),X94) | ~l1_pre_topc(X94) | ~v1_funct_1(X95) | ~v1_funct_2(X95,u1_struct_0(X94),k2_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(X95,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X94),k2_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(X94) | v5_pre_topc(X95,X94,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(backward_demodulation,[],[f532,f585])).
% 1.66/0.61  fof(f532,plain,(
% 1.66/0.61    ( ! [X94,X95] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X94),k2_struct_0(k6_tmap_1(sK0,sK1)),X95,sK2(X94,k6_tmap_1(sK0,sK1),X95)),X94) | ~l1_pre_topc(X94) | ~v1_funct_1(X95) | ~v1_funct_2(X95,u1_struct_0(X94),k2_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(X95,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X94),k2_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(X94) | v5_pre_topc(X95,X94,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f484,f368])).
% 1.66/0.61  fof(f484,plain,(
% 1.66/0.61    ( ! [X94,X95] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X94),k2_struct_0(k6_tmap_1(sK0,sK1)),X95,sK2(X94,k6_tmap_1(sK0,sK1),X95)),X94) | ~l1_pre_topc(X94) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X95) | ~v1_funct_2(X95,u1_struct_0(X94),k2_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(X95,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X94),k2_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(X94) | v5_pre_topc(X95,X94,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(superposition,[],[f59,f412])).
% 1.66/0.61  fof(f59,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X0) != k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) | v5_pre_topc(X2,X0,X1)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f21])).
% 1.66/0.61  fof(f786,plain,(
% 1.66/0.61    v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))),
% 1.66/0.61    inference(forward_demodulation,[],[f785,f541])).
% 1.66/0.61  fof(f785,plain,(
% 1.66/0.61    v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(sK0))),
% 1.66/0.61    inference(forward_demodulation,[],[f780,f580])).
% 1.66/0.61  fof(f780,plain,(
% 1.66/0.61    v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))),
% 1.66/0.61    inference(resolution,[],[f215,f197])).
% 1.66/0.61  fof(f215,plain,(
% 1.66/0.61    ( ! [X12] : (~m1_subset_1(X12,k1_zfmisc_1(k2_struct_0(sK0))) | v1_funct_2(k7_tmap_1(sK0,X12),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X12)))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f207,f193])).
% 1.66/0.61  fof(f207,plain,(
% 1.66/0.61    ( ! [X12] : (~m1_subset_1(X12,k1_zfmisc_1(k2_struct_0(sK0))) | v1_funct_2(k7_tmap_1(sK0,X12),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X12)))) )),
% 1.66/0.61    inference(backward_demodulation,[],[f127,f193])).
% 1.66/0.61  fof(f127,plain,(
% 1.66/0.61    ( ! [X12] : (~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0))) | v1_funct_2(k7_tmap_1(sK0,X12),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X12)))) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f126,f49])).
% 1.66/0.61  fof(f126,plain,(
% 1.66/0.61    ( ! [X12] : (~l1_pre_topc(sK0) | ~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0))) | v1_funct_2(k7_tmap_1(sK0,X12),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X12)))) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f101,f48])).
% 1.66/0.61  fof(f101,plain,(
% 1.66/0.61    ( ! [X12] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X12,k1_zfmisc_1(u1_struct_0(sK0))) | v1_funct_2(k7_tmap_1(sK0,X12),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X12)))) )),
% 1.66/0.61    inference(resolution,[],[f47,f79])).
% 1.66/0.61  fof(f79,plain,(
% 1.66/0.61    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))) )),
% 1.66/0.61    inference(cnf_transformation,[],[f40])).
% 1.66/0.61  fof(f4831,plain,(
% 1.66/0.61    ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)),
% 1.66/0.61    inference(forward_demodulation,[],[f4830,f3271])).
% 1.66/0.61  fof(f3271,plain,(
% 1.66/0.61    k1_xboole_0 = u1_struct_0(k6_tmap_1(sK0,sK1))),
% 1.66/0.61    inference(backward_demodulation,[],[f580,f3243])).
% 1.66/0.61  fof(f4830,plain,(
% 1.66/0.61    ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))),
% 1.66/0.61    inference(subsumption_resolution,[],[f4829,f3291])).
% 1.66/0.61  fof(f3291,plain,(
% 1.66/0.61    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.66/0.61    inference(backward_demodulation,[],[f843,f3243])).
% 1.66/0.61  fof(f4829,plain,(
% 1.66/0.61    ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))),
% 1.66/0.61    inference(forward_demodulation,[],[f4828,f3271])).
% 1.66/0.61  fof(f4828,plain,(
% 1.66/0.61    ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)))),
% 1.66/0.61    inference(subsumption_resolution,[],[f4827,f3861])).
% 1.66/0.61  fof(f3861,plain,(
% 1.66/0.61    ~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))),
% 1.66/0.61    inference(subsumption_resolution,[],[f3860,f3284])).
% 1.66/0.61  fof(f3860,plain,(
% 1.66/0.61    ~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)),
% 1.66/0.61    inference(subsumption_resolution,[],[f3858,f3291])).
% 1.66/0.61  fof(f3858,plain,(
% 1.66/0.61    ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)),
% 1.66/0.61    inference(resolution,[],[f3430,f3460])).
% 1.66/0.61  fof(f3460,plain,(
% 1.66/0.61    v3_pre_topc(sK1,sK0)),
% 1.66/0.61    inference(subsumption_resolution,[],[f3459,f3285])).
% 1.66/0.61  fof(f3285,plain,(
% 1.66/0.61    k6_tmap_1(sK0,sK1) != g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) | v3_pre_topc(sK1,sK0)),
% 1.66/0.61    inference(backward_demodulation,[],[f800,f3243])).
% 1.66/0.61  fof(f3459,plain,(
% 1.66/0.61    v3_pre_topc(sK1,sK0) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),
% 1.66/0.61    inference(forward_demodulation,[],[f3458,f3258])).
% 1.66/0.61  fof(f3258,plain,(
% 1.66/0.61    sK1 = k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1)),
% 1.66/0.61    inference(backward_demodulation,[],[f227,f3243])).
% 1.66/0.61  fof(f3458,plain,(
% 1.66/0.61    v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),sK0) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),
% 1.66/0.61    inference(subsumption_resolution,[],[f3457,f3291])).
% 1.66/0.61  fof(f3457,plain,(
% 1.66/0.61    ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),sK0) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),
% 1.66/0.61    inference(subsumption_resolution,[],[f3382,f3284])).
% 1.66/0.61  fof(f3382,plain,(
% 1.66/0.61    ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),sK0) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),
% 1.66/0.61    inference(trivial_inequality_removal,[],[f3306])).
% 1.66/0.61  fof(f3306,plain,(
% 1.66/0.61    k1_xboole_0 != k1_xboole_0 | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),sK0) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),
% 1.66/0.61    inference(backward_demodulation,[],[f1013,f3243])).
% 1.66/0.61  fof(f1013,plain,(
% 1.66/0.61    ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k1_xboole_0 != k2_struct_0(sK0) | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),sK0) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),
% 1.66/0.61    inference(inner_rewriting,[],[f1012])).
% 1.66/0.61  fof(f1012,plain,(
% 1.66/0.61    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,k1_xboole_0) | k1_xboole_0 != k2_struct_0(sK0) | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k2_struct_0(sK0)),sK1),sK0) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),
% 1.66/0.61    inference(subsumption_resolution,[],[f993,f551])).
% 1.66/0.61  fof(f993,plain,(
% 1.66/0.61    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | k1_xboole_0 != k2_struct_0(sK0) | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k2_struct_0(sK0)),sK1),sK0) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),
% 1.66/0.61    inference(resolution,[],[f970,f830])).
% 1.66/0.61  fof(f970,plain,(
% 1.66/0.61    ( ! [X20] : (~v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(X20,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(X20) | k1_xboole_0 != k2_struct_0(sK0) | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X20,sK1),sK0)) )),
% 1.66/0.61    inference(inner_rewriting,[],[f969])).
% 1.66/0.61  fof(f969,plain,(
% 1.66/0.61    ( ! [X20] : (v3_pre_topc(k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X20,sK1),sK0) | ~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~v1_funct_2(X20,k1_xboole_0,k2_struct_0(sK0)) | ~v1_funct_1(X20) | k1_xboole_0 != k2_struct_0(sK0) | ~v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f968,f580])).
% 1.66/0.61  fof(f968,plain,(
% 1.66/0.61    ( ! [X20] : (~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~v1_funct_2(X20,k1_xboole_0,k2_struct_0(sK0)) | ~v1_funct_1(X20) | k1_xboole_0 != k2_struct_0(sK0) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),sK0) | ~v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f967,f197])).
% 1.66/0.61  fof(f967,plain,(
% 1.66/0.61    ( ! [X20] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~v1_funct_2(X20,k1_xboole_0,k2_struct_0(sK0)) | ~v1_funct_1(X20) | k1_xboole_0 != k2_struct_0(sK0) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),sK0) | ~v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f966,f580])).
% 1.66/0.61  fof(f966,plain,(
% 1.66/0.61    ( ! [X20] : (~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~v1_funct_2(X20,k1_xboole_0,k2_struct_0(sK0)) | ~v1_funct_1(X20) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),sK0) | ~v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f965,f580])).
% 1.66/0.61  fof(f965,plain,(
% 1.66/0.61    ( ! [X20] : (~v1_funct_2(X20,k1_xboole_0,k2_struct_0(sK0)) | ~v1_funct_1(X20) | ~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),sK0) | ~v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f964,f580])).
% 1.66/0.61  fof(f964,plain,(
% 1.66/0.61    ( ! [X20] : (~v1_funct_1(X20) | ~v1_funct_2(X20,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),sK0) | ~v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f950,f368])).
% 1.66/0.61  fof(f950,plain,(
% 1.66/0.61    ( ! [X20] : (~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X20) | ~v1_funct_2(X20,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),sK0) | ~v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(resolution,[],[f322,f796])).
% 1.66/0.61  fof(f322,plain,(
% 1.66/0.61    ( ! [X50,X48,X49] : (~v3_pre_topc(X50,X48) | ~l1_pre_topc(X48) | ~v1_funct_1(X49) | ~v1_funct_2(X49,k1_xboole_0,u1_struct_0(X48)) | ~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X48)))) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X48))) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X48),X49,X50),sK0) | ~v5_pre_topc(X49,sK0,X48)) )),
% 1.66/0.61    inference(inner_rewriting,[],[f321])).
% 1.66/0.61  fof(f321,plain,(
% 1.66/0.61    ( ! [X50,X48,X49] : (v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X48),X49,X50),sK0) | ~l1_pre_topc(X48) | ~v1_funct_1(X49) | ~v1_funct_2(X49,k2_struct_0(sK0),u1_struct_0(X48)) | ~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X48)))) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X48))) | ~v3_pre_topc(X50,X48) | ~v5_pre_topc(X49,sK0,X48)) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f257,f49])).
% 1.66/0.61  fof(f257,plain,(
% 1.66/0.61    ( ! [X50,X48,X49] : (v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X48),X49,X50),sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(X48) | ~v1_funct_1(X49) | ~v1_funct_2(X49,k2_struct_0(sK0),u1_struct_0(X48)) | ~m1_subset_1(X49,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X48)))) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X50,k1_zfmisc_1(u1_struct_0(X48))) | ~v3_pre_topc(X50,X48) | ~v5_pre_topc(X49,sK0,X48)) )),
% 1.66/0.61    inference(superposition,[],[f56,f193])).
% 1.66/0.61  fof(f56,plain,(
% 1.66/0.61    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X0) != k1_xboole_0 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1) | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v5_pre_topc(X2,X0,X1)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f21])).
% 1.66/0.61  fof(f3430,plain,(
% 1.66/0.61    ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)),
% 1.66/0.61    inference(forward_demodulation,[],[f3429,f3243])).
% 1.66/0.61  fof(f3429,plain,(
% 1.66/0.61    ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))),
% 1.66/0.61    inference(forward_demodulation,[],[f3281,f3243])).
% 1.66/0.61  fof(f3281,plain,(
% 1.66/0.61    ~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))),
% 1.66/0.61    inference(backward_demodulation,[],[f624,f3243])).
% 1.66/0.61  fof(f4827,plain,(
% 1.66/0.61    ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))),
% 1.66/0.61    inference(subsumption_resolution,[],[f4826,f3270])).
% 1.66/0.61  fof(f3270,plain,(
% 1.66/0.61    v1_funct_1(k6_partfun1(k1_xboole_0))),
% 1.66/0.61    inference(backward_demodulation,[],[f551,f3243])).
% 1.66/0.61  fof(f4826,plain,(
% 1.66/0.61    ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))),
% 1.66/0.61    inference(subsumption_resolution,[],[f4825,f368])).
% 1.66/0.61  fof(f4825,plain,(
% 1.66/0.61    ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))),
% 1.66/0.61    inference(subsumption_resolution,[],[f4817,f341])).
% 1.66/0.61  fof(f4817,plain,(
% 1.66/0.61    ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))),
% 1.66/0.61    inference(resolution,[],[f4815,f3500])).
% 1.66/0.61  fof(f3500,plain,(
% 1.66/0.61    ( ! [X142,X141] : (~v5_pre_topc(X141,k6_tmap_1(sK0,sK1),X142) | ~m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X142)))) | ~v1_funct_2(X141,k1_xboole_0,u1_struct_0(X142)) | ~v2_pre_topc(X142) | ~l1_pre_topc(X142) | ~v1_funct_1(X141) | v5_pre_topc(X141,sK0,X142)) )),
% 1.66/0.61    inference(duplicate_literal_removal,[],[f3499])).
% 1.66/0.61  fof(f3499,plain,(
% 1.66/0.61    ( ! [X142,X141] : (~v1_funct_2(X141,k1_xboole_0,u1_struct_0(X142)) | ~m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X142)))) | ~v5_pre_topc(X141,k6_tmap_1(sK0,sK1),X142) | ~v1_funct_2(X141,k1_xboole_0,u1_struct_0(X142)) | ~v2_pre_topc(X142) | ~l1_pre_topc(X142) | ~v1_funct_1(X141) | v5_pre_topc(X141,sK0,X142)) )),
% 1.66/0.61    inference(forward_demodulation,[],[f3498,f3271])).
% 1.66/0.61  fof(f3498,plain,(
% 1.66/0.61    ( ! [X142,X141] : (~v1_funct_2(X141,u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X142)) | ~m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X142)))) | ~v5_pre_topc(X141,k6_tmap_1(sK0,sK1),X142) | ~v1_funct_2(X141,k1_xboole_0,u1_struct_0(X142)) | ~v2_pre_topc(X142) | ~l1_pre_topc(X142) | ~v1_funct_1(X141) | v5_pre_topc(X141,sK0,X142)) )),
% 1.66/0.61    inference(forward_demodulation,[],[f3497,f3469])).
% 1.66/0.61  fof(f3469,plain,(
% 1.66/0.61    k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),
% 1.66/0.61    inference(duplicate_literal_removal,[],[f3468])).
% 1.66/0.61  fof(f3468,plain,(
% 1.66/0.61    k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),
% 1.66/0.61    inference(forward_demodulation,[],[f3467,f3258])).
% 1.66/0.61  fof(f3467,plain,(
% 1.66/0.61    g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1)) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),
% 1.66/0.61    inference(subsumption_resolution,[],[f3466,f3245])).
% 1.66/0.61  fof(f3245,plain,(
% 1.66/0.61    m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))),
% 1.66/0.61    inference(backward_demodulation,[],[f197,f3243])).
% 1.66/0.61  fof(f3466,plain,(
% 1.66/0.61    ~m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1)) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),
% 1.66/0.61    inference(forward_demodulation,[],[f3465,f3258])).
% 1.66/0.61  fof(f3465,plain,(
% 1.66/0.61    ~m1_subset_1(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),k1_zfmisc_1(k1_xboole_0)) | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1)) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),
% 1.66/0.61    inference(subsumption_resolution,[],[f3464,f3291])).
% 1.66/0.61  fof(f3464,plain,(
% 1.66/0.61    ~m1_subset_1(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),k1_zfmisc_1(k1_xboole_0)) | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1)) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),
% 1.66/0.61    inference(subsumption_resolution,[],[f3370,f3284])).
% 1.66/0.61  fof(f3370,plain,(
% 1.66/0.61    ~m1_subset_1(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),k1_zfmisc_1(k1_xboole_0)) | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1)) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),
% 1.66/0.61    inference(trivial_inequality_removal,[],[f3319])).
% 1.66/0.61  fof(f3319,plain,(
% 1.66/0.61    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),k1_zfmisc_1(k1_xboole_0)) | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1)) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),
% 1.66/0.61    inference(backward_demodulation,[],[f1129,f3243])).
% 1.66/0.61  fof(f1129,plain,(
% 1.66/0.61    ~m1_subset_1(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),k1_zfmisc_1(k1_xboole_0)) | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1)) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),
% 1.66/0.61    inference(inner_rewriting,[],[f1128])).
% 1.66/0.61  fof(f1128,plain,(
% 1.66/0.61    ~m1_subset_1(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k2_struct_0(sK0)),sK1),k1_zfmisc_1(k1_xboole_0)) | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k2_struct_0(sK0)),sK1)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,k1_xboole_0) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),
% 1.66/0.61    inference(subsumption_resolution,[],[f1109,f551])).
% 1.66/0.61  fof(f1109,plain,(
% 1.66/0.61    ~m1_subset_1(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k2_struct_0(sK0)),sK1),k1_zfmisc_1(k1_xboole_0)) | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k2_struct_0(sK0)),sK1)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k1_xboole_0,k1_xboole_0) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),
% 1.66/0.61    inference(resolution,[],[f1070,f830])).
% 1.66/0.61  fof(f1070,plain,(
% 1.66/0.61    ( ! [X20] : (~v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(k8_relset_1(k1_xboole_0,k1_xboole_0,X20,sK1),k1_zfmisc_1(k1_xboole_0)) | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k1_xboole_0,X20,sK1)) | ~v1_funct_2(X20,k1_xboole_0,k1_xboole_0) | ~v1_funct_1(X20) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))) )),
% 1.66/0.61    inference(inner_rewriting,[],[f1069])).
% 1.66/0.61  fof(f1069,plain,(
% 1.66/0.61    ( ! [X20] : (~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | ~m1_subset_1(k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X20,sK1),k1_zfmisc_1(k1_xboole_0)) | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X20,sK1)) | ~v1_funct_2(X20,k1_xboole_0,k2_struct_0(sK0)) | ~v1_funct_1(X20) | k1_xboole_0 != k2_struct_0(sK0) | ~v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f1068,f580])).
% 1.66/0.61  fof(f1068,plain,(
% 1.66/0.61    ( ! [X20] : (~m1_subset_1(k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X20,sK1),k1_zfmisc_1(k1_xboole_0)) | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X20,sK1)) | ~v1_funct_2(X20,k1_xboole_0,k2_struct_0(sK0)) | ~v1_funct_1(X20) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f1067,f197])).
% 1.66/0.61  fof(f1067,plain,(
% 1.66/0.61    ( ! [X20] : (~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X20,sK1),k1_zfmisc_1(k1_xboole_0)) | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X20,sK1)) | ~v1_funct_2(X20,k1_xboole_0,k2_struct_0(sK0)) | ~v1_funct_1(X20) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f1066,f580])).
% 1.66/0.61  fof(f1066,plain,(
% 1.66/0.61    ( ! [X20] : (~m1_subset_1(k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X20,sK1),k1_zfmisc_1(k1_xboole_0)) | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X20,sK1)) | ~v1_funct_2(X20,k1_xboole_0,k2_struct_0(sK0)) | ~v1_funct_1(X20) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f1065,f580])).
% 1.66/0.61  fof(f1065,plain,(
% 1.66/0.61    ( ! [X20] : (g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X20,sK1)) | ~v1_funct_2(X20,k1_xboole_0,k2_struct_0(sK0)) | ~m1_subset_1(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X20) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f1064,f580])).
% 1.66/0.61  fof(f1064,plain,(
% 1.66/0.61    ( ! [X20] : (~v1_funct_2(X20,k1_xboole_0,k2_struct_0(sK0)) | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1)) | ~m1_subset_1(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X20) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f1063,f580])).
% 1.66/0.61  fof(f1063,plain,(
% 1.66/0.61    ( ! [X20] : (~v1_funct_2(X20,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1)) | ~m1_subset_1(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X20) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f1048,f368])).
% 1.66/0.61  fof(f1048,plain,(
% 1.66/0.61    ( ! [X20] : (~v1_funct_2(X20,k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))) | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1)) | ~m1_subset_1(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),X20,sK1),k1_zfmisc_1(k1_xboole_0)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X20) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~m1_subset_1(X20,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(X20,sK0,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(resolution,[],[f828,f796])).
% 1.66/0.61  fof(f828,plain,(
% 1.66/0.61    ( ! [X6,X4,X5] : (~v3_pre_topc(X6,X4) | ~v1_funct_2(X5,k1_xboole_0,u1_struct_0(X4)) | g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k1_xboole_0,u1_struct_0(X4),X5,X6)) | ~m1_subset_1(k8_relset_1(k1_xboole_0,u1_struct_0(X4),X5,X6),k1_zfmisc_1(k1_xboole_0)) | ~l1_pre_topc(X4) | ~v1_funct_1(X5) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X4)))) | ~v5_pre_topc(X5,sK0,X4)) )),
% 1.66/0.61    inference(inner_rewriting,[],[f827])).
% 1.66/0.61  fof(f827,plain,(
% 1.66/0.61    ( ! [X6,X4,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X4)))) | ~v1_funct_2(X5,k2_struct_0(sK0),u1_struct_0(X4)) | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k2_struct_0(sK0),u1_struct_0(X4),X5,X6)) | ~m1_subset_1(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X4),X5,X6),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(X4) | ~v1_funct_1(X5) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4))) | ~v3_pre_topc(X6,X4) | ~v5_pre_topc(X5,sK0,X4)) )),
% 1.66/0.61    inference(forward_demodulation,[],[f826,f193])).
% 1.66/0.61  fof(f826,plain,(
% 1.66/0.61    ( ! [X6,X4,X5] : (~v1_funct_2(X5,k2_struct_0(sK0),u1_struct_0(X4)) | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k2_struct_0(sK0),u1_struct_0(X4),X5,X6)) | ~m1_subset_1(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X4),X5,X6),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(X4) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4))) | ~v3_pre_topc(X6,X4) | ~v5_pre_topc(X5,sK0,X4)) )),
% 1.66/0.61    inference(forward_demodulation,[],[f825,f193])).
% 1.66/0.61  fof(f825,plain,(
% 1.66/0.61    ( ! [X6,X4,X5] : (g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(k2_struct_0(sK0),u1_struct_0(X4),X5,X6)) | ~m1_subset_1(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X4),X5,X6),k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(X4) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4))) | ~v3_pre_topc(X6,X4) | ~v5_pre_topc(X5,sK0,X4)) )),
% 1.66/0.61    inference(forward_demodulation,[],[f824,f193])).
% 1.66/0.61  fof(f824,plain,(
% 1.66/0.61    ( ! [X6,X4,X5] : (~m1_subset_1(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X4),X5,X6),k1_zfmisc_1(k2_struct_0(sK0))) | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(X4),X5,X6)) | ~l1_pre_topc(X4) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4))) | ~v3_pre_topc(X6,X4) | ~v5_pre_topc(X5,sK0,X4)) )),
% 1.66/0.61    inference(forward_demodulation,[],[f823,f193])).
% 1.66/0.61  fof(f823,plain,(
% 1.66/0.61    ( ! [X6,X4,X5] : (~m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X4),X5,X6),k1_zfmisc_1(k2_struct_0(sK0))) | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(X4),X5,X6)) | ~l1_pre_topc(X4) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4))) | ~v3_pre_topc(X6,X4) | ~v5_pre_topc(X5,sK0,X4)) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f811,f49])).
% 1.66/0.61  fof(f811,plain,(
% 1.66/0.61    ( ! [X6,X4,X5] : (~m1_subset_1(k8_relset_1(u1_struct_0(sK0),u1_struct_0(X4),X5,X6),k1_zfmisc_1(k2_struct_0(sK0))) | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,k8_relset_1(u1_struct_0(sK0),u1_struct_0(X4),X5,X6)) | ~l1_pre_topc(sK0) | ~l1_pre_topc(X4) | ~v1_funct_1(X5) | ~v1_funct_2(X5,u1_struct_0(sK0),u1_struct_0(X4)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X4)))) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X6,k1_zfmisc_1(u1_struct_0(X4))) | ~v3_pre_topc(X6,X4) | ~v5_pre_topc(X5,sK0,X4)) )),
% 1.66/0.61    inference(resolution,[],[f214,f56])).
% 1.66/0.61  fof(f3497,plain,(
% 1.66/0.61    ( ! [X142,X141] : (~m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X142)))) | ~v5_pre_topc(X141,k6_tmap_1(sK0,sK1),X142) | ~v1_funct_2(X141,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X142)) | ~v1_funct_2(X141,k1_xboole_0,u1_struct_0(X142)) | ~v2_pre_topc(X142) | ~l1_pre_topc(X142) | ~v1_funct_1(X141) | v5_pre_topc(X141,sK0,X142)) )),
% 1.66/0.61    inference(duplicate_literal_removal,[],[f3496])).
% 1.66/0.61  fof(f3496,plain,(
% 1.66/0.61    ( ! [X142,X141] : (~m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X142)))) | ~v5_pre_topc(X141,k6_tmap_1(sK0,sK1),X142) | ~v1_funct_2(X141,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X142)) | ~m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X142)))) | ~v1_funct_2(X141,k1_xboole_0,u1_struct_0(X142)) | ~v2_pre_topc(X142) | ~l1_pre_topc(X142) | ~v1_funct_1(X141) | v5_pre_topc(X141,sK0,X142)) )),
% 1.66/0.61    inference(forward_demodulation,[],[f3495,f3271])).
% 1.66/0.61  fof(f3495,plain,(
% 1.66/0.61    ( ! [X142,X141] : (~m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X142)))) | ~v5_pre_topc(X141,k6_tmap_1(sK0,sK1),X142) | ~v1_funct_2(X141,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X142)) | ~m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X142)))) | ~v1_funct_2(X141,k1_xboole_0,u1_struct_0(X142)) | ~v2_pre_topc(X142) | ~l1_pre_topc(X142) | ~v1_funct_1(X141) | v5_pre_topc(X141,sK0,X142)) )),
% 1.66/0.61    inference(forward_demodulation,[],[f3482,f3469])).
% 1.66/0.61  fof(f3482,plain,(
% 1.66/0.61    ( ! [X142,X141] : (~v5_pre_topc(X141,k6_tmap_1(sK0,sK1),X142) | ~m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X142)))) | ~v1_funct_2(X141,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X142)) | ~m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X142)))) | ~v1_funct_2(X141,k1_xboole_0,u1_struct_0(X142)) | ~v2_pre_topc(X142) | ~l1_pre_topc(X142) | ~v1_funct_1(X141) | v5_pre_topc(X141,sK0,X142)) )),
% 1.66/0.61    inference(backward_demodulation,[],[f3419,f3469])).
% 1.66/0.61  fof(f3419,plain,(
% 1.66/0.61    ( ! [X142,X141] : (~m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X142)))) | ~v1_funct_2(X141,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X142)) | ~m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X142)))) | ~v1_funct_2(X141,k1_xboole_0,u1_struct_0(X142)) | ~v5_pre_topc(X141,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X142) | ~v2_pre_topc(X142) | ~l1_pre_topc(X142) | ~v1_funct_1(X141) | v5_pre_topc(X141,sK0,X142)) )),
% 1.66/0.61    inference(forward_demodulation,[],[f3418,f3243])).
% 1.66/0.61  fof(f3418,plain,(
% 1.66/0.61    ( ! [X142,X141] : (~v1_funct_2(X141,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X142)) | ~m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X142)))) | ~v1_funct_2(X141,k1_xboole_0,u1_struct_0(X142)) | ~v5_pre_topc(X141,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X142) | ~v2_pre_topc(X142) | ~l1_pre_topc(X142) | ~v1_funct_1(X141) | ~m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X142)))) | v5_pre_topc(X141,sK0,X142)) )),
% 1.66/0.61    inference(forward_demodulation,[],[f3417,f3243])).
% 1.66/0.61  fof(f3417,plain,(
% 1.66/0.61    ( ! [X142,X141] : (~m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X142)))) | ~v1_funct_2(X141,k1_xboole_0,u1_struct_0(X142)) | ~v5_pre_topc(X141,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X142) | ~v2_pre_topc(X142) | ~l1_pre_topc(X142) | ~v1_funct_1(X141) | ~v1_funct_2(X141,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X142)) | ~m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X142)))) | v5_pre_topc(X141,sK0,X142)) )),
% 1.66/0.61    inference(forward_demodulation,[],[f3416,f3243])).
% 1.66/0.61  fof(f3416,plain,(
% 1.66/0.61    ( ! [X142,X141] : (~v1_funct_2(X141,k1_xboole_0,u1_struct_0(X142)) | ~v5_pre_topc(X141,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X142) | ~v2_pre_topc(X142) | ~l1_pre_topc(X142) | ~v1_funct_1(X141) | ~m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X142)))) | ~v1_funct_2(X141,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X142)) | ~m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X142)))) | v5_pre_topc(X141,sK0,X142)) )),
% 1.66/0.61    inference(forward_demodulation,[],[f3266,f3243])).
% 1.66/0.61  fof(f3266,plain,(
% 1.66/0.61    ( ! [X142,X141] : (~v5_pre_topc(X141,g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X142) | ~v2_pre_topc(X142) | ~l1_pre_topc(X142) | ~v1_funct_1(X141) | ~v1_funct_2(X141,k2_struct_0(sK0),u1_struct_0(X142)) | ~m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X142)))) | ~v1_funct_2(X141,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X142)) | ~m1_subset_1(X141,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X142)))) | v5_pre_topc(X141,sK0,X142)) )),
% 1.66/0.61    inference(backward_demodulation,[],[f330,f3243])).
% 1.66/0.61  fof(f4815,plain,(
% 1.66/0.61    v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))),
% 1.66/0.61    inference(subsumption_resolution,[],[f4814,f3291])).
% 1.66/0.61  fof(f4814,plain,(
% 1.66/0.61    ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))),
% 1.66/0.61    inference(forward_demodulation,[],[f4813,f3271])).
% 1.66/0.61  fof(f4813,plain,(
% 1.66/0.61    v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))))),
% 1.66/0.61    inference(subsumption_resolution,[],[f4812,f3284])).
% 1.66/0.61  fof(f4812,plain,(
% 1.66/0.61    ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))))),
% 1.66/0.61    inference(forward_demodulation,[],[f4811,f3271])).
% 1.66/0.61  fof(f4811,plain,(
% 1.66/0.61    v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1)))))),
% 1.66/0.61    inference(subsumption_resolution,[],[f4810,f3272])).
% 1.66/0.61  fof(f3272,plain,(
% 1.66/0.61    k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))),
% 1.66/0.61    inference(backward_demodulation,[],[f585,f3243])).
% 1.66/0.61  fof(f4810,plain,(
% 1.66/0.61    v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1))),
% 1.66/0.61    inference(subsumption_resolution,[],[f4809,f3270])).
% 1.66/0.61  fof(f4809,plain,(
% 1.66/0.61    v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | ~v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1))),
% 1.66/0.61    inference(subsumption_resolution,[],[f4807,f368])).
% 1.66/0.61  fof(f4807,plain,(
% 1.66/0.61    v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | ~v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1))),
% 1.66/0.61    inference(duplicate_literal_removal,[],[f4805])).
% 1.66/0.61  fof(f4805,plain,(
% 1.66/0.61    v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | ~v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1)) | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))),
% 1.66/0.61    inference(resolution,[],[f4803,f58])).
% 1.66/0.61  fof(f58,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X0) != k1_xboole_0 | v3_pre_topc(sK2(X0,X1,X2),X1) | v5_pre_topc(X2,X0,X1)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f21])).
% 1.66/0.61  fof(f4803,plain,(
% 1.66/0.61    ~v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k6_tmap_1(sK0,sK1)) | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))),
% 1.66/0.61    inference(subsumption_resolution,[],[f4802,f3291])).
% 1.66/0.61  fof(f4802,plain,(
% 1.66/0.61    ~v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k6_tmap_1(sK0,sK1)) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))),
% 1.66/0.61    inference(subsumption_resolution,[],[f4801,f3284])).
% 1.66/0.61  fof(f4801,plain,(
% 1.66/0.61    ~v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))),
% 1.66/0.61    inference(subsumption_resolution,[],[f4799,f3270])).
% 1.66/0.61  fof(f4799,plain,(
% 1.66/0.61    ~v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(k6_partfun1(k1_xboole_0),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))),
% 1.66/0.61    inference(superposition,[],[f3373,f4396])).
% 1.66/0.61  fof(f4396,plain,(
% 1.66/0.61    sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)) = k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)))),
% 1.66/0.61    inference(resolution,[],[f4386,f71])).
% 1.66/0.61  fof(f4386,plain,(
% 1.66/0.61    m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))),
% 1.66/0.61    inference(subsumption_resolution,[],[f4385,f3861])).
% 1.66/0.61  fof(f4385,plain,(
% 1.66/0.61    m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))),
% 1.66/0.61    inference(subsumption_resolution,[],[f4384,f3270])).
% 1.66/0.61  fof(f4384,plain,(
% 1.66/0.61    m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))),
% 1.66/0.61    inference(subsumption_resolution,[],[f4382,f3291])).
% 1.66/0.61  fof(f4382,plain,(
% 1.66/0.61    ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))),
% 1.66/0.61    inference(resolution,[],[f4345,f3284])).
% 1.66/0.61  fof(f4345,plain,(
% 1.66/0.61    ( ! [X5] : (~v1_funct_2(X5,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(X5) | v5_pre_topc(X5,sK0,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f4344,f368])).
% 1.66/0.61  fof(f4344,plain,(
% 1.66/0.61    ( ! [X5] : (~v1_funct_2(X5,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5),k1_zfmisc_1(k1_xboole_0)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X5) | v5_pre_topc(X5,sK0,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f4341,f341])).
% 1.66/0.61  fof(f4341,plain,(
% 1.66/0.61    ( ! [X5] : (~v1_funct_2(X5,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5),k1_zfmisc_1(k1_xboole_0)) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X5) | v5_pre_topc(X5,sK0,k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(superposition,[],[f3594,f3271])).
% 1.66/0.61  fof(f3594,plain,(
% 1.66/0.61    ( ! [X6,X7] : (~v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6)))) | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),X6,X7),k1_zfmisc_1(u1_struct_0(X6))) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | v5_pre_topc(X7,sK0,X6)) )),
% 1.66/0.61    inference(forward_demodulation,[],[f3593,f3469])).
% 1.66/0.61  fof(f3593,plain,(
% 1.66/0.61    ( ! [X6,X7] : (m1_subset_1(sK2(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6))) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6)))) | ~v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6)) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | v5_pre_topc(X7,sK0,X6)) )),
% 1.66/0.61    inference(forward_demodulation,[],[f3592,f3243])).
% 1.66/0.61  fof(f3592,plain,(
% 1.66/0.61    ( ! [X6,X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6)))) | ~v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6)) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | v5_pre_topc(X7,sK0,X6) | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6)))) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f3591,f3272])).
% 1.66/0.61  fof(f3591,plain,(
% 1.66/0.61    ( ! [X6,X7] : (k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6)))) | ~v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6)) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | v5_pre_topc(X7,sK0,X6) | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6)))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f3590,f3469])).
% 1.66/0.61  fof(f3590,plain,(
% 1.66/0.61    ( ! [X6,X7] : (k1_xboole_0 != k2_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6)))) | ~v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6)) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | v5_pre_topc(X7,sK0,X6) | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6)))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f3589,f3243])).
% 1.66/0.61  fof(f3589,plain,(
% 1.66/0.61    ( ! [X6,X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6)))) | ~v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6)) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | v5_pre_topc(X7,sK0,X6) | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6)))) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f3588,f368])).
% 1.66/0.61  fof(f3588,plain,(
% 1.66/0.61    ( ! [X6,X7] : (~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6)))) | ~v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6)) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | v5_pre_topc(X7,sK0,X6) | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6)))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f3587,f3469])).
% 1.66/0.61  fof(f3587,plain,(
% 1.66/0.61    ( ! [X6,X7] : (~l1_pre_topc(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6)))) | ~v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6)) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | v5_pre_topc(X7,sK0,X6) | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6)))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f3586,f3243])).
% 1.66/0.61  fof(f3586,plain,(
% 1.66/0.61    ( ! [X6,X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6)))) | ~v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6)) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | v5_pre_topc(X7,sK0,X6) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6)))) )),
% 1.66/0.61    inference(duplicate_literal_removal,[],[f3585])).
% 1.66/0.61  fof(f3585,plain,(
% 1.66/0.61    ( ! [X6,X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6)))) | ~v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6)))) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | v5_pre_topc(X7,sK0,X6) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6)))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f3584,f3271])).
% 1.66/0.61  fof(f3584,plain,(
% 1.66/0.61    ( ! [X6,X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X6)))) | ~v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6)))) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | v5_pre_topc(X7,sK0,X6) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6)))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f3583,f3469])).
% 1.66/0.61  fof(f3583,plain,(
% 1.66/0.61    ( ! [X6,X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X6)))) | ~v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6)))) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | v5_pre_topc(X7,sK0,X6) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6)))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f3582,f3243])).
% 1.66/0.61  fof(f3582,plain,(
% 1.66/0.61    ( ! [X6,X7] : (~v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6)))) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6)))) | v5_pre_topc(X7,sK0,X6) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6)))) )),
% 1.66/0.61    inference(duplicate_literal_removal,[],[f3581])).
% 1.66/0.61  fof(f3581,plain,(
% 1.66/0.61    ( ! [X6,X7] : (~v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6)))) | ~v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6)) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6)))) | v5_pre_topc(X7,sK0,X6) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6)))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f3580,f3271])).
% 1.66/0.61  fof(f3580,plain,(
% 1.66/0.61    ( ! [X6,X7] : (~v1_funct_2(X7,u1_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X6)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6)))) | ~v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6)) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6)))) | v5_pre_topc(X7,sK0,X6) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6)))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f3579,f3469])).
% 1.66/0.61  fof(f3579,plain,(
% 1.66/0.61    ( ! [X6,X7] : (~v1_funct_2(X7,u1_struct_0(g1_pre_topc(k1_xboole_0,u1_pre_topc(sK0))),u1_struct_0(X6)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6)))) | ~v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6)) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6)))) | v5_pre_topc(X7,sK0,X6) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6)))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f3578,f3243])).
% 1.66/0.61  fof(f3578,plain,(
% 1.66/0.61    ( ! [X6,X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X6)))) | ~v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6)) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6)))) | v5_pre_topc(X7,sK0,X6) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6)))) )),
% 1.66/0.61    inference(forward_demodulation,[],[f3349,f3243])).
% 1.66/0.61  fof(f3349,plain,(
% 1.66/0.61    ( ! [X6,X7] : (~v1_funct_2(X7,k1_xboole_0,u1_struct_0(X6)) | ~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X6)))) | ~v1_funct_2(X7,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6)))) | v5_pre_topc(X7,sK0,X6) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6)))) )),
% 1.66/0.61    inference(backward_demodulation,[],[f2399,f3243])).
% 1.66/0.61  fof(f2399,plain,(
% 1.66/0.61    ( ! [X6,X7] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | ~v1_funct_2(X7,k2_struct_0(sK0),u1_struct_0(X6)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X6)))) | ~v1_funct_2(X7,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6)))) | v5_pre_topc(X7,sK0,X6) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6)))) )),
% 1.66/0.61    inference(duplicate_literal_removal,[],[f2389])).
% 1.66/0.61  fof(f2389,plain,(
% 1.66/0.61    ( ! [X6,X7] : (~v2_pre_topc(X6) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | ~v1_funct_2(X7,k2_struct_0(sK0),u1_struct_0(X6)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X6)))) | ~v1_funct_2(X7,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6)))) | v5_pre_topc(X7,sK0,X6) | ~l1_pre_topc(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | ~l1_pre_topc(X6) | ~v1_funct_1(X7) | ~v1_funct_2(X7,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6)) | ~m1_subset_1(X7,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X6)))) | k1_xboole_0 != k2_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))) | m1_subset_1(sK2(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X6,X7),k1_zfmisc_1(u1_struct_0(X6)))) )),
% 1.66/0.61    inference(resolution,[],[f330,f57])).
% 1.66/0.61  fof(f57,plain,(
% 1.66/0.61    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X0) != k1_xboole_0 | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | v5_pre_topc(X2,X0,X1)) )),
% 1.66/0.61    inference(cnf_transformation,[],[f21])).
% 1.66/0.61  fof(f3373,plain,(
% 1.66/0.61    ( ! [X5] : (~v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X5,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5)),k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X5) | ~v1_funct_2(X5,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(X5,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(trivial_inequality_removal,[],[f3316])).
% 1.66/0.61  fof(f3316,plain,(
% 1.66/0.61    ( ! [X5] : (k1_xboole_0 != k1_xboole_0 | ~v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X5,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5)),k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X5) | ~v1_funct_2(X5,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(X5,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(backward_demodulation,[],[f1089,f3243])).
% 1.66/0.61  fof(f1089,plain,(
% 1.66/0.61    ( ! [X5] : (~v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,X5,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5)),k6_tmap_1(sK0,sK1)) | k1_xboole_0 != k2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,k1_xboole_0,k1_xboole_0) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | v5_pre_topc(X5,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(inner_rewriting,[],[f1088])).
% 1.66/0.61  fof(f1088,plain,(
% 1.66/0.61    ( ! [X5] : (~v3_pre_topc(k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X5,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5)),k6_tmap_1(sK0,sK1)) | k1_xboole_0 != k2_struct_0(sK0) | ~v1_funct_1(X5) | ~v1_funct_2(X5,k1_xboole_0,k2_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | v5_pre_topc(X5,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f1086,f368])).
% 1.66/0.61  fof(f1086,plain,(
% 1.66/0.61    ( ! [X5] : (~v3_pre_topc(k8_relset_1(k1_xboole_0,k2_struct_0(sK0),X5,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X5)),k6_tmap_1(sK0,sK1)) | k1_xboole_0 != k2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X5) | ~v1_funct_2(X5,k1_xboole_0,k2_struct_0(sK0)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_struct_0(sK0)))) | v5_pre_topc(X5,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 1.66/0.61    inference(superposition,[],[f592,f580])).
% 1.66/0.61  fof(f592,plain,(
% 1.66/0.61    ( ! [X92,X93] : (~v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X92),X93,sK2(k6_tmap_1(sK0,sK1),X92,X93)),k6_tmap_1(sK0,sK1)) | k1_xboole_0 != k2_struct_0(sK0) | ~l1_pre_topc(X92) | ~v1_funct_1(X93) | ~v1_funct_2(X93,k1_xboole_0,u1_struct_0(X92)) | ~m1_subset_1(X93,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X92)))) | v5_pre_topc(X93,k6_tmap_1(sK0,sK1),X92)) )),
% 1.66/0.61    inference(backward_demodulation,[],[f531,f585])).
% 1.66/0.61  fof(f531,plain,(
% 1.66/0.61    ( ! [X92,X93] : (~v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(X92),X93,sK2(k6_tmap_1(sK0,sK1),X92,X93)),k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(X92) | ~v1_funct_1(X93) | ~v1_funct_2(X93,k1_xboole_0,u1_struct_0(X92)) | ~m1_subset_1(X93,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,u1_struct_0(X92)))) | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1)) | v5_pre_topc(X93,k6_tmap_1(sK0,sK1),X92)) )),
% 1.66/0.61    inference(inner_rewriting,[],[f530])).
% 1.66/0.61  fof(f530,plain,(
% 1.66/0.61    ( ! [X92,X93] : (~v3_pre_topc(k8_relset_1(k2_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X92),X93,sK2(k6_tmap_1(sK0,sK1),X92,X93)),k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(X92) | ~v1_funct_1(X93) | ~v1_funct_2(X93,k2_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X92)) | ~m1_subset_1(X93,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X92)))) | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1)) | v5_pre_topc(X93,k6_tmap_1(sK0,sK1),X92)) )),
% 1.66/0.61    inference(subsumption_resolution,[],[f483,f368])).
% 1.66/0.61  fof(f483,plain,(
% 1.66/0.61    ( ! [X92,X93] : (~v3_pre_topc(k8_relset_1(k2_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X92),X93,sK2(k6_tmap_1(sK0,sK1),X92,X93)),k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(X92) | ~v1_funct_1(X93) | ~v1_funct_2(X93,k2_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X92)) | ~m1_subset_1(X93,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(k6_tmap_1(sK0,sK1)),u1_struct_0(X92)))) | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1)) | v5_pre_topc(X93,k6_tmap_1(sK0,sK1),X92)) )),
% 1.66/0.61    inference(superposition,[],[f59,f412])).
% 1.66/0.61  % SZS output end Proof for theBenchmark
% 1.66/0.61  % (7579)------------------------------
% 1.66/0.61  % (7579)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.66/0.61  % (7579)Termination reason: Refutation
% 1.66/0.61  
% 1.66/0.61  % (7579)Memory used [KB]: 3454
% 1.66/0.61  % (7579)Time elapsed: 0.205 s
% 1.66/0.61  % (7579)------------------------------
% 1.66/0.61  % (7579)------------------------------
% 1.66/0.61  % (7562)Success in time 0.263 s
%------------------------------------------------------------------------------
