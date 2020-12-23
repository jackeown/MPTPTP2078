%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:19:29 EST 2020

% Result     : Theorem 1.78s
% Output     : Refutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :  338 (1077109 expanded)
%              Number of leaves         :   13 (212786 expanded)
%              Depth                    :   72
%              Number of atoms          : 1476 (5204765 expanded)
%              Number of equality atoms :  214 (305252 expanded)
%              Maximal formula depth    :   15 (   6 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f5862,plain,(
    $false ),
    inference(subsumption_resolution,[],[f5860,f5250])).

fof(f5250,plain,(
    v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0) ),
    inference(subsumption_resolution,[],[f5249,f4329])).

fof(f4329,plain,(
    m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) ),
    inference(subsumption_resolution,[],[f4260,f4328])).

fof(f4328,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(duplicate_literal_removal,[],[f4327])).

fof(f4327,plain,
    ( v3_pre_topc(sK1,sK0)
    | v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f4326,f4186])).

fof(f4186,plain,(
    sK1 = k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1) ),
    inference(backward_demodulation,[],[f218,f4170])).

fof(f4170,plain,(
    k1_xboole_0 = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f4169,f2398])).

fof(f2398,plain,
    ( v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),sK0)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2397,f2256])).

fof(f2256,plain,
    ( m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(resolution,[],[f2248,f2201])).

fof(f2201,plain,
    ( v3_pre_topc(sK1,sK0)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f2200])).

fof(f2200,plain,
    ( v3_pre_topc(sK1,sK0)
    | k1_xboole_0 = k2_struct_0(sK0)
    | v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f2199,f1981])).

fof(f1981,plain,(
    sK1 = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK1) ),
    inference(superposition,[],[f1934,f218])).

fof(f1934,plain,(
    ! [X0] : k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),X0) = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),X0) ),
    inference(resolution,[],[f1907,f82])).

fof(f82,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f1907,plain,(
    m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f1906,f656])).

fof(f656,plain,(
    k7_tmap_1(sK0,sK1) = k6_partfun1(k2_struct_0(sK0)) ),
    inference(resolution,[],[f203,f188])).

fof(f188,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f47,f184])).

fof(f184,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f147,f51])).

fof(f51,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f147,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f50,f52])).

fof(f52,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f50,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
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
    inference(flattening,[],[f17])).

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
    inference(ennf_transformation,[],[f16])).

fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f47,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f203,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k7_tmap_1(sK0,X0) = k6_partfun1(k2_struct_0(sK0)) ) ),
    inference(forward_demodulation,[],[f190,f184])).

fof(f190,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0)) ) ),
    inference(backward_demodulation,[],[f106,f184])).

fof(f106,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f105,f50])).

fof(f105,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0)) ) ),
    inference(subsumption_resolution,[],[f87,f49])).

fof(f49,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f87,plain,(
    ! [X0] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
      | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0)) ) ),
    inference(resolution,[],[f48,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_tmap_1)).

fof(f48,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f1906,plain,(
    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f1895,f740])).

fof(f740,plain,(
    u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(sK0) ),
    inference(resolution,[],[f204,f188])).

fof(f204,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | u1_struct_0(k6_tmap_1(sK0,X1)) = k2_struct_0(sK0) ) ),
    inference(forward_demodulation,[],[f191,f184])).

fof(f191,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1)) ) ),
    inference(backward_demodulation,[],[f108,f184])).

fof(f108,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f107,f50])).

fof(f107,plain,(
    ! [X1] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1)) ) ),
    inference(subsumption_resolution,[],[f88,f49])).

fof(f88,plain,(
    ! [X1] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1)) ) ),
    inference(resolution,[],[f48,f67])).

fof(f67,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
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
         => ( k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f1895,plain,(
    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    inference(resolution,[],[f206,f188])).

fof(f206,plain,(
    ! [X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(k7_tmap_1(sK0,X10),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X10))))) ) ),
    inference(forward_demodulation,[],[f199,f184])).

fof(f199,plain,(
    ! [X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(k7_tmap_1(sK0,X10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X10))))) ) ),
    inference(backward_demodulation,[],[f124,f184])).

fof(f124,plain,(
    ! [X10] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k7_tmap_1(sK0,X10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X10))))) ) ),
    inference(subsumption_resolution,[],[f123,f50])).

fof(f123,plain,(
    ! [X10] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k7_tmap_1(sK0,X10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X10))))) ) ),
    inference(subsumption_resolution,[],[f97,f49])).

fof(f97,plain,(
    ! [X10] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0)))
      | m1_subset_1(k7_tmap_1(sK0,X10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X10))))) ) ),
    inference(resolution,[],[f48,f81])).

fof(f81,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f2199,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | v3_pre_topc(sK1,sK0)
    | v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK1),sK0) ),
    inference(subsumption_resolution,[],[f2194,f188])).

fof(f2194,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | k1_xboole_0 = k2_struct_0(sK0)
    | v3_pre_topc(sK1,sK0)
    | v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK1),sK0) ),
    inference(resolution,[],[f1940,f1861])).

fof(f1861,plain,(
    v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1860,f188])).

fof(f1860,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f1847])).

fof(f1847,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) ),
    inference(superposition,[],[f200,f740])).

fof(f200,plain,(
    ! [X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X11))))
      | ~ m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK0)))
      | v3_pre_topc(X11,k6_tmap_1(sK0,X11)) ) ),
    inference(backward_demodulation,[],[f126,f184])).

fof(f126,plain,(
    ! [X11] :
      ( ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X11))))
      | v3_pre_topc(X11,k6_tmap_1(sK0,X11)) ) ),
    inference(subsumption_resolution,[],[f125,f50])).

fof(f125,plain,(
    ! [X11] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X11))))
      | v3_pre_topc(X11,k6_tmap_1(sK0,X11)) ) ),
    inference(subsumption_resolution,[],[f98,f49])).

fof(f98,plain,(
    ! [X11] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X11))))
      | v3_pre_topc(X11,k6_tmap_1(sK0,X11)) ) ),
    inference(resolution,[],[f48,f83])).

fof(f83,plain,(
    ! [X2,X0] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2))))
      | v3_pre_topc(X2,k6_tmap_1(X0,X2)) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
      | X1 != X2
      | v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
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
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f1940,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | k1_xboole_0 = k2_struct_0(sK0)
      | v3_pre_topc(sK1,sK0)
      | v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),X0),sK0) ) ),
    inference(backward_demodulation,[],[f755,f1934])).

fof(f755,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),X0),sK0)
      | k1_xboole_0 = k2_struct_0(sK0)
      | v3_pre_topc(sK1,sK0)
      | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f754,f746])).

fof(f746,plain,(
    k2_struct_0(sK0) = k2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f427,f740])).

fof(f427,plain,(
    u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f370,f51])).

fof(f370,plain,(
    l1_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f364,f52])).

fof(f364,plain,(
    l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f196,f188])).

fof(f196,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0)))
      | l1_pre_topc(k6_tmap_1(sK0,X7)) ) ),
    inference(backward_demodulation,[],[f118,f184])).

fof(f118,plain,(
    ! [X7] :
      ( ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | l1_pre_topc(k6_tmap_1(sK0,X7)) ) ),
    inference(subsumption_resolution,[],[f117,f50])).

fof(f117,plain,(
    ! [X7] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | l1_pre_topc(k6_tmap_1(sK0,X7)) ) ),
    inference(subsumption_resolution,[],[f94,f49])).

fof(f94,plain,(
    ! [X7] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0)))
      | l1_pre_topc(k6_tmap_1(sK0,X7)) ) ),
    inference(resolution,[],[f48,f78])).

fof(f78,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f754,plain,(
    ! [X0] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),X0),sK0)
      | k1_xboole_0 = k2_struct_0(sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK0,sK1))))
      | v3_pre_topc(sK1,sK0)
      | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f751,f746])).

fof(f751,plain,(
    ! [X0] :
      ( k1_xboole_0 = k2_struct_0(sK0)
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK0,sK1))))
      | v3_pre_topc(sK1,sK0)
      | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) ) ),
    inference(backward_demodulation,[],[f667,f746])).

fof(f667,plain,(
    ! [X0] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK0,sK1))))
      | v3_pre_topc(sK1,sK0)
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) ) ),
    inference(backward_demodulation,[],[f436,f656])).

fof(f436,plain,(
    ! [X0] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X0),sK0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK0,sK1))))
      | v3_pre_topc(sK1,sK0)
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f432,f427])).

fof(f432,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK0,sK1))))
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X0),sK0)
      | v3_pre_topc(sK1,sK0)
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) ) ),
    inference(backward_demodulation,[],[f417,f427])).

fof(f417,plain,(
    ! [X0] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X0),sK0)
      | v3_pre_topc(sK1,sK0)
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f416,f184])).

fof(f416,plain,(
    ! [X0] :
      ( v3_pre_topc(sK1,sK0)
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1))
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X0),sK0) ) ),
    inference(subsumption_resolution,[],[f415,f187])).

fof(f187,plain,
    ( m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f46,f184])).

fof(f46,plain,
    ( m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f415,plain,(
    ! [X0] :
      ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | v3_pre_topc(sK1,sK0)
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1))
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X0),sK0) ) ),
    inference(forward_demodulation,[],[f414,f184])).

fof(f414,plain,(
    ! [X0] :
      ( v3_pre_topc(sK1,sK0)
      | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1))
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X0),sK0) ) ),
    inference(subsumption_resolution,[],[f413,f186])).

fof(f186,plain,
    ( v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f44,f184])).

fof(f44,plain,
    ( v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f413,plain,(
    ! [X0] :
      ( ~ v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
      | v3_pre_topc(sK1,sK0)
      | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1))
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X0),sK0) ) ),
    inference(forward_demodulation,[],[f412,f184])).

fof(f412,plain,(
    ! [X0] :
      ( v3_pre_topc(sK1,sK0)
      | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1))
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X0),sK0) ) ),
    inference(subsumption_resolution,[],[f411,f43])).

fof(f43,plain,
    ( v1_funct_1(k7_tmap_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f411,plain,(
    ! [X0] :
      ( v3_pre_topc(sK1,sK0)
      | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
      | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1))
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X0),sK0) ) ),
    inference(subsumption_resolution,[],[f410,f364])).

fof(f410,plain,(
    ! [X0] :
      ( v3_pre_topc(sK1,sK0)
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
      | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1))
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X0),sK0) ) ),
    inference(subsumption_resolution,[],[f407,f50])).

fof(f407,plain,(
    ! [X0] :
      ( v3_pre_topc(sK1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
      | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1))
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X0),sK0) ) ),
    inference(resolution,[],[f45,f53])).

fof(f53,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f45,plain,
    ( v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f2248,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(subsumption_resolution,[],[f2242,f1907])).

fof(f2242,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(resolution,[],[f1335,f1801])).

fof(f1801,plain,(
    v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f1800,f656])).

fof(f1800,plain,(
    v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f1789,f740])).

fof(f1789,plain,(
    v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f205,f188])).

fof(f205,plain,(
    ! [X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0)))
      | v1_funct_2(k7_tmap_1(sK0,X9),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X9))) ) ),
    inference(forward_demodulation,[],[f198,f184])).

fof(f198,plain,(
    ! [X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0)))
      | v1_funct_2(k7_tmap_1(sK0,X9),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X9))) ) ),
    inference(backward_demodulation,[],[f122,f184])).

fof(f122,plain,(
    ! [X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_funct_2(k7_tmap_1(sK0,X9),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X9))) ) ),
    inference(subsumption_resolution,[],[f121,f50])).

fof(f121,plain,(
    ! [X9] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_funct_2(k7_tmap_1(sK0,X9),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X9))) ) ),
    inference(subsumption_resolution,[],[f96,f49])).

fof(f96,plain,(
    ! [X9] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_funct_2(k7_tmap_1(sK0,X9),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X9))) ) ),
    inference(resolution,[],[f48,f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1335,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f1334,f1302])).

fof(f1302,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | k1_xboole_0 = k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f1301,f740])).

fof(f1301,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f1300,f746])).

fof(f1300,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ),
    inference(duplicate_literal_removal,[],[f1299])).

fof(f1299,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v3_pre_topc(sK1,sK0)
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f1298,f184])).

fof(f1298,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v3_pre_topc(sK1,sK0)
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f1297,f740])).

fof(f1297,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ),
    inference(duplicate_literal_removal,[],[f1296])).

fof(f1296,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f1295,f184])).

fof(f1295,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f1294,f740])).

fof(f1294,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f1293,f669])).

fof(f669,plain,(
    v1_funct_1(k6_partfun1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f478,f656])).

fof(f478,plain,(
    v1_funct_1(k7_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f197,f188])).

fof(f197,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK0)))
      | v1_funct_1(k7_tmap_1(sK0,X8)) ) ),
    inference(backward_demodulation,[],[f120,f184])).

fof(f120,plain,(
    ! [X8] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_funct_1(k7_tmap_1(sK0,X8)) ) ),
    inference(subsumption_resolution,[],[f119,f50])).

fof(f119,plain,(
    ! [X8] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_funct_1(k7_tmap_1(sK0,X8)) ) ),
    inference(subsumption_resolution,[],[f95,f49])).

fof(f95,plain,(
    ! [X8] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0)))
      | v1_funct_1(k7_tmap_1(sK0,X8)) ) ),
    inference(resolution,[],[f48,f79])).

fof(f79,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | v1_funct_1(k7_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f1293,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f1292,f364])).

fof(f1292,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f1282,f50])).

fof(f1282,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ),
    inference(resolution,[],[f757,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_struct_0(X1) = k1_xboole_0
      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f757,plain,
    ( ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f756,f746])).

fof(f756,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f752,f669])).

fof(f752,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f672,f746])).

fof(f672,plain,
    ( ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f671,f656])).

fof(f671,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f670,f656])).

fof(f670,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f666,f656])).

fof(f666,plain,
    ( ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f434,f656])).

fof(f434,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f430,f427])).

fof(f430,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f202,f427])).

fof(f202,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f185,f184])).

fof(f185,plain,
    ( ~ v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f42,f184])).

fof(f42,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f18])).

fof(f1334,plain,
    ( m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | k1_xboole_0 != k2_struct_0(sK0) ),
    inference(forward_demodulation,[],[f1333,f740])).

fof(f1333,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | k1_xboole_0 != k2_struct_0(sK0)
    | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ),
    inference(duplicate_literal_removal,[],[f1332])).

fof(f1332,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v3_pre_topc(sK1,sK0)
    | k1_xboole_0 != k2_struct_0(sK0)
    | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f1331,f184])).

fof(f1331,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v3_pre_topc(sK1,sK0)
    | k1_xboole_0 != k2_struct_0(sK0)
    | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f1330,f740])).

fof(f1330,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(sK0)
    | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ),
    inference(duplicate_literal_removal,[],[f1329])).

fof(f1329,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(sK0)
    | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f1328,f184])).

fof(f1328,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(sK0)
    | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ),
    inference(forward_demodulation,[],[f1327,f740])).

fof(f1327,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(sK0)
    | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f1326,f669])).

fof(f1326,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(sK0)
    | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f1325,f364])).

fof(f1325,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(sK0)
    | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ),
    inference(subsumption_resolution,[],[f1285,f50])).

fof(f1285,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(sK0)
    | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) ),
    inference(resolution,[],[f757,f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_struct_0(X0) != k1_xboole_0
      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f2397,plain,
    ( ~ m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | k1_xboole_0 = k2_struct_0(sK0)
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),sK0) ),
    inference(forward_demodulation,[],[f2396,f184])).

fof(f2396,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),sK0) ),
    inference(subsumption_resolution,[],[f2389,f50])).

fof(f2389,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),sK0) ),
    inference(resolution,[],[f2385,f61])).

fof(f61,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ r2_hidden(X1,u1_pre_topc(X0))
      | v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).

fof(f2385,plain,
    ( r2_hidden(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),u1_pre_topc(sK0))
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(duplicate_literal_removal,[],[f2383])).

fof(f2383,plain,
    ( r2_hidden(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),u1_pre_topc(sK0))
    | k1_xboole_0 = k2_struct_0(sK0)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(superposition,[],[f2377,f2208])).

fof(f2208,plain,
    ( u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2203,f188])).

fof(f2203,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f2201,f1688])).

fof(f1688,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,sK0)
      | u1_pre_topc(sK0) = k5_tmap_1(sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(duplicate_literal_removal,[],[f1687])).

fof(f1687,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | u1_pre_topc(sK0) = k5_tmap_1(sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0) ) ),
    inference(forward_demodulation,[],[f1686,f184])).

fof(f1686,plain,(
    ! [X1] :
      ( u1_pre_topc(sK0) = k5_tmap_1(sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0) ) ),
    inference(subsumption_resolution,[],[f1685,f50])).

fof(f1685,plain,(
    ! [X1] :
      ( u1_pre_topc(sK0) = k5_tmap_1(sK0,X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
      | ~ v3_pre_topc(X1,sK0) ) ),
    inference(resolution,[],[f194,f62])).

fof(f62,plain,(
    ! [X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | r2_hidden(X1,u1_pre_topc(X0))
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f194,plain,(
    ! [X4] :
      ( ~ r2_hidden(X4,u1_pre_topc(sK0))
      | u1_pre_topc(sK0) = k5_tmap_1(sK0,X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(backward_demodulation,[],[f114,f184])).

fof(f114,plain,(
    ! [X4] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_pre_topc(sK0) = k5_tmap_1(sK0,X4)
      | ~ r2_hidden(X4,u1_pre_topc(sK0)) ) ),
    inference(subsumption_resolution,[],[f113,f50])).

fof(f113,plain,(
    ! [X4] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_pre_topc(sK0) = k5_tmap_1(sK0,X4)
      | ~ r2_hidden(X4,u1_pre_topc(sK0)) ) ),
    inference(subsumption_resolution,[],[f91,f49])).

fof(f91,plain,(
    ! [X4] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0)))
      | u1_pre_topc(sK0) = k5_tmap_1(sK0,X4)
      | ~ r2_hidden(X4,u1_pre_topc(sK0)) ) ),
    inference(resolution,[],[f48,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | u1_pre_topc(X0) = k5_tmap_1(X0,X1)
      | ~ r2_hidden(X1,u1_pre_topc(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) )
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
         => ( r2_hidden(X1,u1_pre_topc(X0))
          <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).

fof(f2377,plain,
    ( r2_hidden(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k5_tmap_1(sK0,sK1))
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f2368,f2256])).

fof(f2368,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | r2_hidden(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k5_tmap_1(sK0,sK1))
    | ~ m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(resolution,[],[f2358,f1463])).

fof(f1463,plain,(
    ! [X3] :
      ( ~ v3_pre_topc(X3,k6_tmap_1(sK0,sK1))
      | r2_hidden(X3,k5_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0))) ) ),
    inference(forward_demodulation,[],[f1462,f740])).

fof(f1462,plain,(
    ! [X3] :
      ( r2_hidden(X3,k5_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | ~ v3_pre_topc(X3,k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f1459,f364])).

fof(f1459,plain,(
    ! [X3] :
      ( r2_hidden(X3,k5_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | ~ v3_pre_topc(X3,k6_tmap_1(sK0,sK1)) ) ),
    inference(superposition,[],[f62,f1446])).

fof(f1446,plain,(
    u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f192,f188])).

fof(f192,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0)))
      | k5_tmap_1(sK0,X2) = u1_pre_topc(k6_tmap_1(sK0,X2)) ) ),
    inference(backward_demodulation,[],[f110,f184])).

fof(f110,plain,(
    ! [X2] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k5_tmap_1(sK0,X2) = u1_pre_topc(k6_tmap_1(sK0,X2)) ) ),
    inference(subsumption_resolution,[],[f109,f50])).

fof(f109,plain,(
    ! [X2] :
      ( ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k5_tmap_1(sK0,X2) = u1_pre_topc(k6_tmap_1(sK0,X2)) ) ),
    inference(subsumption_resolution,[],[f89,f49])).

fof(f89,plain,(
    ! [X2] :
      ( ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0)))
      | k5_tmap_1(sK0,X2) = u1_pre_topc(k6_tmap_1(sK0,X2)) ) ),
    inference(resolution,[],[f48,f68])).

fof(f68,plain,(
    ! [X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f2358,plain,
    ( v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(resolution,[],[f2357,f2201])).

fof(f2357,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2351,f1907])).

fof(f2351,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v3_pre_topc(sK1,sK0)
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f1345,f1801])).

fof(f1345,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v3_pre_topc(sK1,sK0)
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f1344])).

fof(f1344,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v3_pre_topc(sK1,sK0)
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1343,f184])).

fof(f1343,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v3_pre_topc(sK1,sK0)
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1342,f740])).

fof(f1342,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f1341])).

fof(f1341,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1340,f184])).

fof(f1340,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1339,f740])).

fof(f1339,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1338,f1312])).

fof(f1312,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | k1_xboole_0 = k2_struct_0(sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1311,f746])).

fof(f1311,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f1310])).

fof(f1310,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v3_pre_topc(sK1,sK0)
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1309,f184])).

fof(f1309,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v3_pre_topc(sK1,sK0)
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1308,f740])).

fof(f1308,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    inference(duplicate_literal_removal,[],[f1307])).

fof(f1307,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1306,f184])).

fof(f1306,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f1305,f740])).

fof(f1305,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1304,f669])).

fof(f1304,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1303,f364])).

fof(f1303,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1283,f50])).

fof(f1283,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f757,f55])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_struct_0(X1) = k1_xboole_0
      | v3_pre_topc(sK2(X0,X1,X2),X1)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1338,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(sK0)
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1337,f669])).

fof(f1337,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(sK0)
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1336,f364])).

fof(f1336,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(sK0)
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1286,f50])).

fof(f1286,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(sK0)
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f757,f59])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_struct_0(X0) != k1_xboole_0
      | v3_pre_topc(sK2(X0,X1,X2),X1)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f4169,plain,
    ( ~ v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),sK0)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(subsumption_resolution,[],[f4168,f2201])).

fof(f4168,plain,
    ( ~ v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),sK0)
    | ~ v3_pre_topc(sK1,sK0)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(superposition,[],[f1944,f3977])).

fof(f3977,plain,
    ( sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))))
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(superposition,[],[f2268,f1934])).

fof(f2268,plain,
    ( sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))))
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(resolution,[],[f2256,f75])).

fof(f75,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).

fof(f1944,plain,
    ( ~ v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f1943,f1801])).

fof(f1943,plain,
    ( ~ v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f1941,f1907])).

fof(f1941,plain,
    ( ~ v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f1357,f1934])).

fof(f1357,plain,
    ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f1356,f1324])).

fof(f1324,plain,
    ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)
    | k1_xboole_0 = k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f1323,f184])).

fof(f1323,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)
    | k1_xboole_0 = k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f1322,f740])).

fof(f1322,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) ),
    inference(forward_demodulation,[],[f1321,f746])).

fof(f1321,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) ),
    inference(duplicate_literal_removal,[],[f1320])).

fof(f1320,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v3_pre_topc(sK1,sK0)
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) ),
    inference(forward_demodulation,[],[f1319,f184])).

fof(f1319,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v3_pre_topc(sK1,sK0)
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) ),
    inference(forward_demodulation,[],[f1318,f740])).

fof(f1318,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) ),
    inference(duplicate_literal_removal,[],[f1317])).

fof(f1317,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) ),
    inference(forward_demodulation,[],[f1316,f184])).

fof(f1316,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) ),
    inference(forward_demodulation,[],[f1315,f740])).

fof(f1315,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f1314,f669])).

fof(f1314,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f1313,f364])).

fof(f1313,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f1284,f50])).

fof(f1284,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) ),
    inference(resolution,[],[f757,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_struct_0(X1) = k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f1356,plain,
    ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | k1_xboole_0 != k2_struct_0(sK0) ),
    inference(forward_demodulation,[],[f1355,f184])).

fof(f1355,plain,
    ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | k1_xboole_0 != k2_struct_0(sK0) ),
    inference(forward_demodulation,[],[f1354,f740])).

fof(f1354,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) ),
    inference(duplicate_literal_removal,[],[f1353])).

fof(f1353,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v3_pre_topc(sK1,sK0)
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) ),
    inference(forward_demodulation,[],[f1352,f184])).

fof(f1352,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v3_pre_topc(sK1,sK0)
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) ),
    inference(forward_demodulation,[],[f1351,f740])).

fof(f1351,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) ),
    inference(duplicate_literal_removal,[],[f1350])).

fof(f1350,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) ),
    inference(forward_demodulation,[],[f1349,f184])).

fof(f1349,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) ),
    inference(forward_demodulation,[],[f1348,f740])).

fof(f1348,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f1347,f669])).

fof(f1347,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f1346,f364])).

fof(f1346,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) ),
    inference(subsumption_resolution,[],[f1287,f50])).

fof(f1287,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) ),
    inference(resolution,[],[f757,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ l1_pre_topc(X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_struct_0(X0) != k1_xboole_0
      | ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f218,plain,(
    sK1 = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1) ),
    inference(resolution,[],[f188,f75])).

fof(f4326,plain,
    ( v3_pre_topc(sK1,sK0)
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),sK0) ),
    inference(subsumption_resolution,[],[f4311,f4172])).

fof(f4172,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f188,f4170])).

fof(f4311,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | v3_pre_topc(sK1,sK0)
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),sK0) ),
    inference(trivial_inequality_removal,[],[f4256])).

fof(f4256,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | v3_pre_topc(sK1,sK0)
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),sK0) ),
    inference(backward_demodulation,[],[f2078,f4170])).

fof(f2078,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | v3_pre_topc(sK1,sK0)
    | k1_xboole_0 != k2_struct_0(sK0)
    | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),sK0) ),
    inference(resolution,[],[f759,f1861])).

fof(f759,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | v3_pre_topc(sK1,sK0)
      | k1_xboole_0 != k2_struct_0(sK0)
      | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X1),sK0) ) ),
    inference(inner_rewriting,[],[f758])).

fof(f758,plain,(
    ! [X1] :
      ( v3_pre_topc(k8_relset_1(k1_xboole_0,k2_struct_0(sK0),k6_partfun1(k1_xboole_0),X1),sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | v3_pre_topc(sK1,sK0)
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f753,f746])).

fof(f753,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))
      | v3_pre_topc(k8_relset_1(k1_xboole_0,k2_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),X1),sK0)
      | v3_pre_topc(sK1,sK0)
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) ) ),
    inference(backward_demodulation,[],[f673,f746])).

fof(f673,plain,(
    ! [X1] :
      ( v3_pre_topc(k8_relset_1(k1_xboole_0,k2_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),X1),sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK0,sK1))))
      | v3_pre_topc(sK1,sK0)
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) ) ),
    inference(inner_rewriting,[],[f668])).

fof(f668,plain,(
    ! [X1] :
      ( v3_pre_topc(k8_relset_1(k1_xboole_0,k2_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),X1),sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK0,sK1))))
      | v3_pre_topc(sK1,sK0)
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) ) ),
    inference(backward_demodulation,[],[f437,f656])).

fof(f437,plain,(
    ! [X1] :
      ( v3_pre_topc(k8_relset_1(k1_xboole_0,k2_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X1),sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK0,sK1))))
      | v3_pre_topc(sK1,sK0)
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f433,f427])).

fof(f433,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK0,sK1))))
      | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X1),sK0)
      | v3_pre_topc(sK1,sK0)
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) ) ),
    inference(backward_demodulation,[],[f426,f427])).

fof(f426,plain,(
    ! [X1] :
      ( v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X1),sK0)
      | v3_pre_topc(sK1,sK0)
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) ) ),
    inference(inner_rewriting,[],[f425])).

fof(f425,plain,(
    ! [X1] :
      ( v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X1),sK0)
      | v3_pre_topc(sK1,sK0)
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f424,f184])).

fof(f424,plain,(
    ! [X1] :
      ( v3_pre_topc(sK1,sK0)
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1))
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X1),sK0) ) ),
    inference(subsumption_resolution,[],[f423,f187])).

fof(f423,plain,(
    ! [X1] :
      ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | v3_pre_topc(sK1,sK0)
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1))
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X1),sK0) ) ),
    inference(forward_demodulation,[],[f422,f184])).

fof(f422,plain,(
    ! [X1] :
      ( v3_pre_topc(sK1,sK0)
      | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1))
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X1),sK0) ) ),
    inference(subsumption_resolution,[],[f421,f186])).

fof(f421,plain,(
    ! [X1] :
      ( ~ v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
      | v3_pre_topc(sK1,sK0)
      | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1))
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X1),sK0) ) ),
    inference(forward_demodulation,[],[f420,f184])).

fof(f420,plain,(
    ! [X1] :
      ( v3_pre_topc(sK1,sK0)
      | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1))
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X1),sK0) ) ),
    inference(subsumption_resolution,[],[f419,f43])).

fof(f419,plain,(
    ! [X1] :
      ( v3_pre_topc(sK1,sK0)
      | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
      | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1))
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X1),sK0) ) ),
    inference(subsumption_resolution,[],[f418,f364])).

fof(f418,plain,(
    ! [X1] :
      ( v3_pre_topc(sK1,sK0)
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
      | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1))
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X1),sK0) ) ),
    inference(subsumption_resolution,[],[f408,f50])).

fof(f408,plain,(
    ! [X1] :
      ( v3_pre_topc(sK1,sK0)
      | ~ l1_pre_topc(sK0)
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
      | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
      | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))
      | ~ v3_pre_topc(X1,k6_tmap_1(sK0,sK1))
      | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X1),sK0) ) ),
    inference(resolution,[],[f45,f57])).

fof(f57,plain,(
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
    inference(cnf_transformation,[],[f22])).

fof(f4260,plain,
    ( m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f2248,f4170])).

fof(f5249,plain,
    ( ~ m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0) ),
    inference(forward_demodulation,[],[f5248,f4171])).

fof(f4171,plain,(
    k1_xboole_0 = u1_struct_0(sK0) ),
    inference(backward_demodulation,[],[f184,f4170])).

fof(f5248,plain,
    ( ~ m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0) ),
    inference(subsumption_resolution,[],[f5243,f50])).

fof(f5243,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0) ),
    inference(resolution,[],[f5239,f61])).

fof(f5239,plain,(
    r2_hidden(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f5230,f4329])).

fof(f5230,plain,
    ( ~ m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))
    | r2_hidden(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f5113,f4330])).

fof(f4330,plain,(
    v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f4261,f4328])).

fof(f4261,plain,
    ( v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f2357,f4170])).

fof(f5113,plain,(
    ! [X3] :
      ( ~ v3_pre_topc(X3,k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | r2_hidden(X3,u1_pre_topc(sK0)) ) ),
    inference(backward_demodulation,[],[f4226,f5107])).

fof(f5107,plain,(
    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    inference(subsumption_resolution,[],[f5099,f4172])).

fof(f5099,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))
    | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) ),
    inference(resolution,[],[f4231,f4328])).

fof(f4231,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(X1,sK0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0))
      | u1_pre_topc(sK0) = k5_tmap_1(sK0,X1) ) ),
    inference(backward_demodulation,[],[f1688,f4170])).

fof(f4226,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
      | ~ v3_pre_topc(X3,k6_tmap_1(sK0,sK1))
      | r2_hidden(X3,k5_tmap_1(sK0,sK1)) ) ),
    inference(backward_demodulation,[],[f1463,f4170])).

fof(f5860,plain,(
    ~ v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0) ),
    inference(backward_demodulation,[],[f4725,f5856])).

fof(f5856,plain,(
    sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)) = k10_relat_1(k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))) ),
    inference(superposition,[],[f4737,f4242])).

fof(f4242,plain,(
    ! [X0] : k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X0) = k10_relat_1(k6_partfun1(k1_xboole_0),X0) ),
    inference(backward_demodulation,[],[f1934,f4170])).

fof(f4737,plain,(
    sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)) = k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))) ),
    inference(resolution,[],[f4329,f75])).

fof(f4725,plain,(
    ~ v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0) ),
    inference(forward_demodulation,[],[f4724,f4242])).

fof(f4724,plain,(
    ~ v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0) ),
    inference(forward_demodulation,[],[f4723,f4171])).

fof(f4723,plain,(
    ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0) ),
    inference(forward_demodulation,[],[f4722,f4195])).

fof(f4195,plain,(
    k1_xboole_0 = u1_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f740,f4170])).

fof(f4722,plain,(
    ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0) ),
    inference(subsumption_resolution,[],[f4721,f4241])).

fof(f4241,plain,(
    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f1907,f4170])).

fof(f4721,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0) ),
    inference(forward_demodulation,[],[f4720,f4171])).

fof(f4720,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0)))
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0) ),
    inference(forward_demodulation,[],[f4719,f4195])).

fof(f4719,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0) ),
    inference(subsumption_resolution,[],[f4718,f4239])).

fof(f4239,plain,(
    v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f1801,f4170])).

fof(f4718,plain,
    ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0) ),
    inference(forward_demodulation,[],[f4717,f4171])).

fof(f4717,plain,
    ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(sK0),k1_xboole_0)
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0) ),
    inference(forward_demodulation,[],[f4716,f4195])).

fof(f4716,plain,
    ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0) ),
    inference(subsumption_resolution,[],[f4715,f4170])).

fof(f4715,plain,
    ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0) ),
    inference(subsumption_resolution,[],[f4714,f4194])).

fof(f4194,plain,(
    v1_funct_1(k6_partfun1(k1_xboole_0)) ),
    inference(backward_demodulation,[],[f669,f4170])).

fof(f4714,plain,
    ( ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0) ),
    inference(subsumption_resolution,[],[f4713,f364])).

fof(f4713,plain,
    ( ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0) ),
    inference(subsumption_resolution,[],[f4712,f50])).

fof(f4712,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0) ),
    inference(subsumption_resolution,[],[f4711,f4328])).

fof(f4711,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0) ),
    inference(subsumption_resolution,[],[f4710,f4241])).

fof(f4710,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0) ),
    inference(subsumption_resolution,[],[f4695,f4239])).

fof(f4695,plain,
    ( ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v3_pre_topc(sK1,sK0)
    | ~ l1_pre_topc(sK0)
    | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k1_xboole_0))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | k1_xboole_0 != k2_struct_0(sK0)
    | ~ v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0) ),
    inference(resolution,[],[f4320,f60])).

fof(f4320,plain,
    ( ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f4319,f4170])).

fof(f4319,plain,
    ( ~ v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f4202,f4170])).

fof(f4202,plain,
    ( ~ m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f757,f4170])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 11:33:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.20/0.45  % (30248)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.46  % (30255)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  % (30247)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.48  % (30242)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.48  % (30242)Refutation not found, incomplete strategy% (30242)------------------------------
% 0.20/0.48  % (30242)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (30256)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.48  % (30257)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.48  % (30242)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.48  
% 0.20/0.48  % (30242)Memory used [KB]: 6140
% 0.20/0.48  % (30242)Time elapsed: 0.071 s
% 0.20/0.48  % (30242)------------------------------
% 0.20/0.48  % (30242)------------------------------
% 0.20/0.49  % (30249)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.49  % (30254)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.49  % (30245)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (30244)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.49  % (30258)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.50  % (30261)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.50  % (30260)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.50  % (30246)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.50  % (30243)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (30252)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.51  % (30243)Refutation not found, incomplete strategy% (30243)------------------------------
% 0.20/0.51  % (30243)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (30243)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (30243)Memory used [KB]: 10618
% 0.20/0.51  % (30243)Time elapsed: 0.091 s
% 0.20/0.51  % (30243)------------------------------
% 0.20/0.51  % (30243)------------------------------
% 0.20/0.51  % (30252)Refutation not found, incomplete strategy% (30252)------------------------------
% 0.20/0.51  % (30252)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (30254)Refutation not found, incomplete strategy% (30254)------------------------------
% 0.20/0.51  % (30254)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (30254)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (30254)Memory used [KB]: 6140
% 0.20/0.51  % (30254)Time elapsed: 0.092 s
% 0.20/0.51  % (30254)------------------------------
% 0.20/0.51  % (30254)------------------------------
% 0.20/0.51  % (30252)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (30252)Memory used [KB]: 6140
% 0.20/0.51  % (30252)Time elapsed: 0.093 s
% 0.20/0.51  % (30252)------------------------------
% 0.20/0.51  % (30252)------------------------------
% 0.20/0.51  % (30253)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.20/0.51  % (30262)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.51  % (30251)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.51  % (30262)Refutation not found, incomplete strategy% (30262)------------------------------
% 0.20/0.51  % (30262)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.51  % (30262)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.51  
% 0.20/0.51  % (30262)Memory used [KB]: 10618
% 0.20/0.51  % (30262)Time elapsed: 0.108 s
% 0.20/0.51  % (30262)------------------------------
% 0.20/0.51  % (30262)------------------------------
% 0.20/0.52  % (30250)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.52  % (30259)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 1.78/0.58  % (30255)Refutation found. Thanks to Tanya!
% 1.78/0.58  % SZS status Theorem for theBenchmark
% 1.78/0.58  % SZS output start Proof for theBenchmark
% 1.78/0.58  fof(f5862,plain,(
% 1.78/0.58    $false),
% 1.78/0.58    inference(subsumption_resolution,[],[f5860,f5250])).
% 1.78/0.58  fof(f5250,plain,(
% 1.78/0.58    v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f5249,f4329])).
% 1.78/0.58  fof(f4329,plain,(
% 1.78/0.58    m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0))),
% 1.78/0.58    inference(subsumption_resolution,[],[f4260,f4328])).
% 1.78/0.58  fof(f4328,plain,(
% 1.78/0.58    v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(duplicate_literal_removal,[],[f4327])).
% 1.78/0.58  fof(f4327,plain,(
% 1.78/0.58    v3_pre_topc(sK1,sK0) | v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(forward_demodulation,[],[f4326,f4186])).
% 1.78/0.58  fof(f4186,plain,(
% 1.78/0.58    sK1 = k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1)),
% 1.78/0.58    inference(backward_demodulation,[],[f218,f4170])).
% 1.78/0.58  fof(f4170,plain,(
% 1.78/0.58    k1_xboole_0 = k2_struct_0(sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f4169,f2398])).
% 1.78/0.58  fof(f2398,plain,(
% 1.78/0.58    v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),sK0) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f2397,f2256])).
% 1.78/0.58  fof(f2256,plain,(
% 1.78/0.58    m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.78/0.58    inference(resolution,[],[f2248,f2201])).
% 1.78/0.58  fof(f2201,plain,(
% 1.78/0.58    v3_pre_topc(sK1,sK0) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.78/0.58    inference(duplicate_literal_removal,[],[f2200])).
% 1.78/0.58  fof(f2200,plain,(
% 1.78/0.58    v3_pre_topc(sK1,sK0) | k1_xboole_0 = k2_struct_0(sK0) | v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(forward_demodulation,[],[f2199,f1981])).
% 1.78/0.58  fof(f1981,plain,(
% 1.78/0.58    sK1 = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK1)),
% 1.78/0.58    inference(superposition,[],[f1934,f218])).
% 1.78/0.58  fof(f1934,plain,(
% 1.78/0.58    ( ! [X0] : (k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),X0) = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),X0)) )),
% 1.78/0.58    inference(resolution,[],[f1907,f82])).
% 1.78/0.58  fof(f82,plain,(
% 1.78/0.58    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 1.78/0.58    inference(cnf_transformation,[],[f41])).
% 1.78/0.58  fof(f41,plain,(
% 1.78/0.58    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.78/0.58    inference(ennf_transformation,[],[f1])).
% 1.78/0.58  fof(f1,axiom,(
% 1.78/0.58    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.78/0.58  fof(f1907,plain,(
% 1.78/0.58    m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))),
% 1.78/0.58    inference(forward_demodulation,[],[f1906,f656])).
% 1.78/0.58  fof(f656,plain,(
% 1.78/0.58    k7_tmap_1(sK0,sK1) = k6_partfun1(k2_struct_0(sK0))),
% 1.78/0.58    inference(resolution,[],[f203,f188])).
% 1.78/0.58  fof(f188,plain,(
% 1.78/0.58    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.78/0.58    inference(backward_demodulation,[],[f47,f184])).
% 1.78/0.58  fof(f184,plain,(
% 1.78/0.58    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.78/0.58    inference(resolution,[],[f147,f51])).
% 1.78/0.58  fof(f51,plain,(
% 1.78/0.58    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.78/0.58    inference(cnf_transformation,[],[f19])).
% 1.78/0.58  fof(f19,plain,(
% 1.78/0.58    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.78/0.58    inference(ennf_transformation,[],[f3])).
% 1.78/0.58  fof(f3,axiom,(
% 1.78/0.58    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 1.78/0.58  fof(f147,plain,(
% 1.78/0.58    l1_struct_0(sK0)),
% 1.78/0.58    inference(resolution,[],[f50,f52])).
% 1.78/0.58  fof(f52,plain,(
% 1.78/0.58    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 1.78/0.58    inference(cnf_transformation,[],[f20])).
% 1.78/0.58  fof(f20,plain,(
% 1.78/0.58    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.78/0.58    inference(ennf_transformation,[],[f5])).
% 1.78/0.58  fof(f5,axiom,(
% 1.78/0.58    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.78/0.58  fof(f50,plain,(
% 1.78/0.58    l1_pre_topc(sK0)),
% 1.78/0.58    inference(cnf_transformation,[],[f18])).
% 1.78/0.58  fof(f18,plain,(
% 1.78/0.58    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 1.78/0.58    inference(flattening,[],[f17])).
% 1.78/0.58  fof(f17,plain,(
% 1.78/0.58    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 1.78/0.58    inference(ennf_transformation,[],[f16])).
% 1.78/0.58  fof(f16,negated_conjecture,(
% 1.78/0.58    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 1.78/0.58    inference(negated_conjecture,[],[f15])).
% 1.78/0.58  fof(f15,conjecture,(
% 1.78/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_tmap_1)).
% 1.78/0.58  fof(f47,plain,(
% 1.78/0.58    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 1.78/0.58    inference(cnf_transformation,[],[f18])).
% 1.78/0.58  fof(f203,plain,(
% 1.78/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k7_tmap_1(sK0,X0) = k6_partfun1(k2_struct_0(sK0))) )),
% 1.78/0.58    inference(forward_demodulation,[],[f190,f184])).
% 1.78/0.58  fof(f190,plain,(
% 1.78/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0))) )),
% 1.78/0.58    inference(backward_demodulation,[],[f106,f184])).
% 1.78/0.58  fof(f106,plain,(
% 1.78/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0))) )),
% 1.78/0.58    inference(subsumption_resolution,[],[f105,f50])).
% 1.78/0.58  fof(f105,plain,(
% 1.78/0.58    ( ! [X0] : (~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0))) )),
% 1.78/0.58    inference(subsumption_resolution,[],[f87,f49])).
% 1.78/0.58  fof(f49,plain,(
% 1.78/0.58    v2_pre_topc(sK0)),
% 1.78/0.58    inference(cnf_transformation,[],[f18])).
% 1.78/0.58  fof(f87,plain,(
% 1.78/0.58    ( ! [X0] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_tmap_1(sK0,X0) = k6_partfun1(u1_struct_0(sK0))) )),
% 1.78/0.58    inference(resolution,[],[f48,f66])).
% 1.78/0.58  fof(f66,plain,(
% 1.78/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))) )),
% 1.78/0.58    inference(cnf_transformation,[],[f27])).
% 1.78/0.58  fof(f27,plain,(
% 1.78/0.58    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/0.58    inference(flattening,[],[f26])).
% 1.78/0.58  fof(f26,plain,(
% 1.78/0.58    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.78/0.58    inference(ennf_transformation,[],[f8])).
% 1.78/0.58  fof(f8,axiom,(
% 1.78/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_tmap_1)).
% 1.78/0.58  fof(f48,plain,(
% 1.78/0.58    ~v2_struct_0(sK0)),
% 1.78/0.58    inference(cnf_transformation,[],[f18])).
% 1.78/0.58  fof(f1906,plain,(
% 1.78/0.58    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))),
% 1.78/0.58    inference(forward_demodulation,[],[f1895,f740])).
% 1.78/0.58  fof(f740,plain,(
% 1.78/0.58    u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(sK0)),
% 1.78/0.58    inference(resolution,[],[f204,f188])).
% 1.78/0.58  fof(f204,plain,(
% 1.78/0.58    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | u1_struct_0(k6_tmap_1(sK0,X1)) = k2_struct_0(sK0)) )),
% 1.78/0.58    inference(forward_demodulation,[],[f191,f184])).
% 1.78/0.58  fof(f191,plain,(
% 1.78/0.58    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1))) )),
% 1.78/0.58    inference(backward_demodulation,[],[f108,f184])).
% 1.78/0.58  fof(f108,plain,(
% 1.78/0.58    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1))) )),
% 1.78/0.58    inference(subsumption_resolution,[],[f107,f50])).
% 1.78/0.58  fof(f107,plain,(
% 1.78/0.58    ( ! [X1] : (~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1))) )),
% 1.78/0.58    inference(subsumption_resolution,[],[f88,f49])).
% 1.78/0.58  fof(f88,plain,(
% 1.78/0.58    ( ! [X1] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | u1_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X1))) )),
% 1.78/0.58    inference(resolution,[],[f48,f67])).
% 1.78/0.58  fof(f67,plain,(
% 1.78/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) )),
% 1.78/0.58    inference(cnf_transformation,[],[f29])).
% 1.78/0.58  fof(f29,plain,(
% 1.78/0.58    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/0.58    inference(flattening,[],[f28])).
% 1.78/0.58  fof(f28,plain,(
% 1.78/0.58    ! [X0] : (! [X1] : ((k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.78/0.58    inference(ennf_transformation,[],[f13])).
% 1.78/0.58  fof(f13,axiom,(
% 1.78/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1)) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t104_tmap_1)).
% 1.78/0.58  fof(f1895,plain,(
% 1.78/0.58    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))),
% 1.78/0.58    inference(resolution,[],[f206,f188])).
% 1.78/0.58  fof(f206,plain,(
% 1.78/0.58    ( ! [X10] : (~m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k7_tmap_1(sK0,X10),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X10)))))) )),
% 1.78/0.58    inference(forward_demodulation,[],[f199,f184])).
% 1.78/0.58  fof(f199,plain,(
% 1.78/0.58    ( ! [X10] : (~m1_subset_1(X10,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k7_tmap_1(sK0,X10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X10)))))) )),
% 1.78/0.58    inference(backward_demodulation,[],[f124,f184])).
% 1.78/0.58  fof(f124,plain,(
% 1.78/0.58    ( ! [X10] : (~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k7_tmap_1(sK0,X10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X10)))))) )),
% 1.78/0.58    inference(subsumption_resolution,[],[f123,f50])).
% 1.78/0.58  fof(f123,plain,(
% 1.78/0.58    ( ! [X10] : (~l1_pre_topc(sK0) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k7_tmap_1(sK0,X10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X10)))))) )),
% 1.78/0.58    inference(subsumption_resolution,[],[f97,f49])).
% 1.78/0.58  fof(f97,plain,(
% 1.78/0.58    ( ! [X10] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X10,k1_zfmisc_1(u1_struct_0(sK0))) | m1_subset_1(k7_tmap_1(sK0,X10),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X10)))))) )),
% 1.78/0.58    inference(resolution,[],[f48,f81])).
% 1.78/0.58  fof(f81,plain,(
% 1.78/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))) )),
% 1.78/0.58    inference(cnf_transformation,[],[f40])).
% 1.78/0.58  fof(f40,plain,(
% 1.78/0.58    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/0.58    inference(flattening,[],[f39])).
% 1.78/0.58  fof(f39,plain,(
% 1.78/0.58    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.78/0.58    inference(ennf_transformation,[],[f10])).
% 1.78/0.58  fof(f10,axiom,(
% 1.78/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 1.78/0.58  fof(f2199,plain,(
% 1.78/0.58    k1_xboole_0 = k2_struct_0(sK0) | v3_pre_topc(sK1,sK0) | v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK1),sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f2194,f188])).
% 1.78/0.58  fof(f2194,plain,(
% 1.78/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = k2_struct_0(sK0) | v3_pre_topc(sK1,sK0) | v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK1),sK0)),
% 1.78/0.58    inference(resolution,[],[f1940,f1861])).
% 1.78/0.58  fof(f1861,plain,(
% 1.78/0.58    v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(subsumption_resolution,[],[f1860,f188])).
% 1.78/0.58  fof(f1860,plain,(
% 1.78/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(duplicate_literal_removal,[],[f1847])).
% 1.78/0.58  fof(f1847,plain,(
% 1.78/0.58    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(superposition,[],[f200,f740])).
% 1.78/0.58  fof(f200,plain,(
% 1.78/0.58    ( ! [X11] : (~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X11)))) | ~m1_subset_1(X11,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(X11,k6_tmap_1(sK0,X11))) )),
% 1.78/0.58    inference(backward_demodulation,[],[f126,f184])).
% 1.78/0.58  fof(f126,plain,(
% 1.78/0.58    ( ! [X11] : (~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X11)))) | v3_pre_topc(X11,k6_tmap_1(sK0,X11))) )),
% 1.78/0.58    inference(subsumption_resolution,[],[f125,f50])).
% 1.78/0.58  fof(f125,plain,(
% 1.78/0.58    ( ! [X11] : (~l1_pre_topc(sK0) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X11)))) | v3_pre_topc(X11,k6_tmap_1(sK0,X11))) )),
% 1.78/0.58    inference(subsumption_resolution,[],[f98,f49])).
% 1.78/0.58  fof(f98,plain,(
% 1.78/0.58    ( ! [X11] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X11,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,X11)))) | v3_pre_topc(X11,k6_tmap_1(sK0,X11))) )),
% 1.78/0.58    inference(resolution,[],[f48,f83])).
% 1.78/0.58  fof(f83,plain,(
% 1.78/0.58    ( ! [X2,X0] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2)))) | v3_pre_topc(X2,k6_tmap_1(X0,X2))) )),
% 1.78/0.58    inference(equality_resolution,[],[f71])).
% 1.78/0.58  fof(f71,plain,(
% 1.78/0.58    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) | X1 != X2 | v3_pre_topc(X2,k6_tmap_1(X0,X1))) )),
% 1.78/0.58    inference(cnf_transformation,[],[f33])).
% 1.78/0.58  fof(f33,plain,(
% 1.78/0.58    ! [X0] : (! [X1] : (! [X2] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/0.58    inference(flattening,[],[f32])).
% 1.78/0.58  fof(f32,plain,(
% 1.78/0.58    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.78/0.58    inference(ennf_transformation,[],[f14])).
% 1.78/0.58  fof(f14,axiom,(
% 1.78/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) => (X1 = X2 => v3_pre_topc(X2,k6_tmap_1(X0,X1))))))),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t105_tmap_1)).
% 1.78/0.58  fof(f1940,plain,(
% 1.78/0.58    ( ! [X0] : (~v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = k2_struct_0(sK0) | v3_pre_topc(sK1,sK0) | v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),X0),sK0)) )),
% 1.78/0.58    inference(backward_demodulation,[],[f755,f1934])).
% 1.78/0.58  fof(f755,plain,(
% 1.78/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),X0),sK0) | k1_xboole_0 = k2_struct_0(sK0) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1))) )),
% 1.78/0.58    inference(forward_demodulation,[],[f754,f746])).
% 1.78/0.58  fof(f746,plain,(
% 1.78/0.58    k2_struct_0(sK0) = k2_struct_0(k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(backward_demodulation,[],[f427,f740])).
% 1.78/0.58  fof(f427,plain,(
% 1.78/0.58    u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(resolution,[],[f370,f51])).
% 1.78/0.58  fof(f370,plain,(
% 1.78/0.58    l1_struct_0(k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(resolution,[],[f364,f52])).
% 1.78/0.58  fof(f364,plain,(
% 1.78/0.58    l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(resolution,[],[f196,f188])).
% 1.78/0.58  fof(f196,plain,(
% 1.78/0.58    ( ! [X7] : (~m1_subset_1(X7,k1_zfmisc_1(k2_struct_0(sK0))) | l1_pre_topc(k6_tmap_1(sK0,X7))) )),
% 1.78/0.58    inference(backward_demodulation,[],[f118,f184])).
% 1.78/0.58  fof(f118,plain,(
% 1.78/0.58    ( ! [X7] : (~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | l1_pre_topc(k6_tmap_1(sK0,X7))) )),
% 1.78/0.58    inference(subsumption_resolution,[],[f117,f50])).
% 1.78/0.58  fof(f117,plain,(
% 1.78/0.58    ( ! [X7] : (~l1_pre_topc(sK0) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | l1_pre_topc(k6_tmap_1(sK0,X7))) )),
% 1.78/0.58    inference(subsumption_resolution,[],[f94,f49])).
% 1.78/0.58  fof(f94,plain,(
% 1.78/0.58    ( ! [X7] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X7,k1_zfmisc_1(u1_struct_0(sK0))) | l1_pre_topc(k6_tmap_1(sK0,X7))) )),
% 1.78/0.58    inference(resolution,[],[f48,f78])).
% 1.78/0.58  fof(f78,plain,(
% 1.78/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | l1_pre_topc(k6_tmap_1(X0,X1))) )),
% 1.78/0.58    inference(cnf_transformation,[],[f38])).
% 1.78/0.58  fof(f38,plain,(
% 1.78/0.58    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/0.58    inference(flattening,[],[f37])).
% 1.78/0.58  fof(f37,plain,(
% 1.78/0.58    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.78/0.58    inference(ennf_transformation,[],[f9])).
% 1.78/0.58  fof(f9,axiom,(
% 1.78/0.58    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 1.78/0.58  fof(f754,plain,(
% 1.78/0.58    ( ! [X0] : (v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),X0),sK0) | k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK0,sK1)))) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1))) )),
% 1.78/0.58    inference(forward_demodulation,[],[f751,f746])).
% 1.78/0.58  fof(f751,plain,(
% 1.78/0.58    ( ! [X0] : (k1_xboole_0 = k2_struct_0(sK0) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK0,sK1)))) | v3_pre_topc(sK1,sK0) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1))) )),
% 1.78/0.58    inference(backward_demodulation,[],[f667,f746])).
% 1.78/0.58  fof(f667,plain,(
% 1.78/0.58    ( ! [X0] : (v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK0,sK1)))) | v3_pre_topc(sK1,sK0) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1))) )),
% 1.78/0.58    inference(backward_demodulation,[],[f436,f656])).
% 1.78/0.58  fof(f436,plain,(
% 1.78/0.58    ( ! [X0] : (v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X0),sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK0,sK1)))) | v3_pre_topc(sK1,sK0) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1))) )),
% 1.78/0.58    inference(forward_demodulation,[],[f432,f427])).
% 1.78/0.58  fof(f432,plain,(
% 1.78/0.58    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK0,sK1)))) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X0),sK0) | v3_pre_topc(sK1,sK0) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1))) )),
% 1.78/0.58    inference(backward_demodulation,[],[f417,f427])).
% 1.78/0.58  fof(f417,plain,(
% 1.78/0.58    ( ! [X0] : (v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X0),sK0) | v3_pre_topc(sK1,sK0) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1))) )),
% 1.78/0.58    inference(forward_demodulation,[],[f416,f184])).
% 1.78/0.58  fof(f416,plain,(
% 1.78/0.58    ( ! [X0] : (v3_pre_topc(sK1,sK0) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X0),sK0)) )),
% 1.78/0.58    inference(subsumption_resolution,[],[f415,f187])).
% 1.78/0.58  fof(f187,plain,(
% 1.78/0.58    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(backward_demodulation,[],[f46,f184])).
% 1.78/0.58  fof(f46,plain,(
% 1.78/0.58    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(cnf_transformation,[],[f18])).
% 1.78/0.58  fof(f415,plain,(
% 1.78/0.58    ( ! [X0] : (~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | v3_pre_topc(sK1,sK0) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X0),sK0)) )),
% 1.78/0.58    inference(forward_demodulation,[],[f414,f184])).
% 1.78/0.58  fof(f414,plain,(
% 1.78/0.58    ( ! [X0] : (v3_pre_topc(sK1,sK0) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X0),sK0)) )),
% 1.78/0.58    inference(subsumption_resolution,[],[f413,f186])).
% 1.78/0.58  fof(f186,plain,(
% 1.78/0.58    v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(backward_demodulation,[],[f44,f184])).
% 1.78/0.58  fof(f44,plain,(
% 1.78/0.58    v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(cnf_transformation,[],[f18])).
% 1.78/0.58  fof(f413,plain,(
% 1.78/0.58    ( ! [X0] : (~v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | v3_pre_topc(sK1,sK0) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X0),sK0)) )),
% 1.78/0.58    inference(forward_demodulation,[],[f412,f184])).
% 1.78/0.58  fof(f412,plain,(
% 1.78/0.58    ( ! [X0] : (v3_pre_topc(sK1,sK0) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X0),sK0)) )),
% 1.78/0.58    inference(subsumption_resolution,[],[f411,f43])).
% 1.78/0.58  fof(f43,plain,(
% 1.78/0.58    v1_funct_1(k7_tmap_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(cnf_transformation,[],[f18])).
% 1.78/0.58  fof(f411,plain,(
% 1.78/0.58    ( ! [X0] : (v3_pre_topc(sK1,sK0) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X0),sK0)) )),
% 1.78/0.58    inference(subsumption_resolution,[],[f410,f364])).
% 1.78/0.58  fof(f410,plain,(
% 1.78/0.58    ( ! [X0] : (v3_pre_topc(sK1,sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X0),sK0)) )),
% 1.78/0.58    inference(subsumption_resolution,[],[f407,f50])).
% 1.78/0.58  fof(f407,plain,(
% 1.78/0.58    ( ! [X0] : (v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X0),sK0)) )),
% 1.78/0.58    inference(resolution,[],[f45,f53])).
% 1.78/0.58  fof(f53,plain,(
% 1.78/0.58    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1) | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v5_pre_topc(X2,X0,X1)) )),
% 1.78/0.58    inference(cnf_transformation,[],[f22])).
% 1.78/0.58  fof(f22,plain,(
% 1.78/0.58    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.78/0.58    inference(flattening,[],[f21])).
% 1.78/0.58  fof(f21,plain,(
% 1.78/0.58    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 1.78/0.58    inference(ennf_transformation,[],[f7])).
% 1.78/0.58  fof(f7,axiom,(
% 1.78/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_struct_0(X1) = k1_xboole_0 => k2_struct_0(X0) = k1_xboole_0) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_tops_2)).
% 1.78/0.58  fof(f45,plain,(
% 1.78/0.58    v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(cnf_transformation,[],[f18])).
% 1.78/0.58  fof(f2248,plain,(
% 1.78/0.58    ~v3_pre_topc(sK1,sK0) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.78/0.58    inference(subsumption_resolution,[],[f2242,f1907])).
% 1.78/0.58  fof(f2242,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(resolution,[],[f1335,f1801])).
% 1.78/0.58  fof(f1801,plain,(
% 1.78/0.58    v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))),
% 1.78/0.58    inference(forward_demodulation,[],[f1800,f656])).
% 1.78/0.58  fof(f1800,plain,(
% 1.78/0.58    v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(sK0))),
% 1.78/0.58    inference(forward_demodulation,[],[f1789,f740])).
% 1.78/0.58  fof(f1789,plain,(
% 1.78/0.58    v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))),
% 1.78/0.58    inference(resolution,[],[f205,f188])).
% 1.78/0.58  fof(f205,plain,(
% 1.78/0.58    ( ! [X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0))) | v1_funct_2(k7_tmap_1(sK0,X9),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X9)))) )),
% 1.78/0.58    inference(forward_demodulation,[],[f198,f184])).
% 1.78/0.58  fof(f198,plain,(
% 1.78/0.58    ( ! [X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_struct_0(sK0))) | v1_funct_2(k7_tmap_1(sK0,X9),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X9)))) )),
% 1.78/0.58    inference(backward_demodulation,[],[f122,f184])).
% 1.78/0.58  fof(f122,plain,(
% 1.78/0.58    ( ! [X9] : (~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) | v1_funct_2(k7_tmap_1(sK0,X9),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X9)))) )),
% 1.78/0.58    inference(subsumption_resolution,[],[f121,f50])).
% 1.78/0.58  fof(f121,plain,(
% 1.78/0.58    ( ! [X9] : (~l1_pre_topc(sK0) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) | v1_funct_2(k7_tmap_1(sK0,X9),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X9)))) )),
% 1.78/0.58    inference(subsumption_resolution,[],[f96,f49])).
% 1.78/0.58  fof(f96,plain,(
% 1.78/0.58    ( ! [X9] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X9,k1_zfmisc_1(u1_struct_0(sK0))) | v1_funct_2(k7_tmap_1(sK0,X9),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X9)))) )),
% 1.78/0.58    inference(resolution,[],[f48,f80])).
% 1.78/0.58  fof(f80,plain,(
% 1.78/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))) )),
% 1.78/0.58    inference(cnf_transformation,[],[f40])).
% 1.78/0.58  fof(f1335,plain,(
% 1.78/0.58    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f1334,f1302])).
% 1.78/0.58  fof(f1302,plain,(
% 1.78/0.58    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(forward_demodulation,[],[f1301,f740])).
% 1.78/0.58  fof(f1301,plain,(
% 1.78/0.58    k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))),
% 1.78/0.58    inference(forward_demodulation,[],[f1300,f746])).
% 1.78/0.58  fof(f1300,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))),
% 1.78/0.58    inference(duplicate_literal_removal,[],[f1299])).
% 1.78/0.58  fof(f1299,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v3_pre_topc(sK1,sK0) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))),
% 1.78/0.58    inference(forward_demodulation,[],[f1298,f184])).
% 1.78/0.58  fof(f1298,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v3_pre_topc(sK1,sK0) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))),
% 1.78/0.58    inference(forward_demodulation,[],[f1297,f740])).
% 1.78/0.58  fof(f1297,plain,(
% 1.78/0.58    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))),
% 1.78/0.58    inference(duplicate_literal_removal,[],[f1296])).
% 1.78/0.58  fof(f1296,plain,(
% 1.78/0.58    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))),
% 1.78/0.58    inference(forward_demodulation,[],[f1295,f184])).
% 1.78/0.58  fof(f1295,plain,(
% 1.78/0.58    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))),
% 1.78/0.58    inference(forward_demodulation,[],[f1294,f740])).
% 1.78/0.58  fof(f1294,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))),
% 1.78/0.58    inference(subsumption_resolution,[],[f1293,f669])).
% 1.78/0.58  fof(f669,plain,(
% 1.78/0.58    v1_funct_1(k6_partfun1(k2_struct_0(sK0)))),
% 1.78/0.58    inference(backward_demodulation,[],[f478,f656])).
% 1.78/0.58  fof(f478,plain,(
% 1.78/0.58    v1_funct_1(k7_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(resolution,[],[f197,f188])).
% 1.78/0.58  fof(f197,plain,(
% 1.78/0.58    ( ! [X8] : (~m1_subset_1(X8,k1_zfmisc_1(k2_struct_0(sK0))) | v1_funct_1(k7_tmap_1(sK0,X8))) )),
% 1.78/0.58    inference(backward_demodulation,[],[f120,f184])).
% 1.78/0.58  fof(f120,plain,(
% 1.78/0.58    ( ! [X8] : (~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | v1_funct_1(k7_tmap_1(sK0,X8))) )),
% 1.78/0.58    inference(subsumption_resolution,[],[f119,f50])).
% 1.78/0.58  fof(f119,plain,(
% 1.78/0.58    ( ! [X8] : (~l1_pre_topc(sK0) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | v1_funct_1(k7_tmap_1(sK0,X8))) )),
% 1.78/0.58    inference(subsumption_resolution,[],[f95,f49])).
% 1.78/0.58  fof(f95,plain,(
% 1.78/0.58    ( ! [X8] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X8,k1_zfmisc_1(u1_struct_0(sK0))) | v1_funct_1(k7_tmap_1(sK0,X8))) )),
% 1.78/0.58    inference(resolution,[],[f48,f79])).
% 1.78/0.58  fof(f79,plain,(
% 1.78/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | v1_funct_1(k7_tmap_1(X0,X1))) )),
% 1.78/0.58    inference(cnf_transformation,[],[f40])).
% 1.78/0.58  fof(f1293,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))),
% 1.78/0.58    inference(subsumption_resolution,[],[f1292,f364])).
% 1.78/0.58  fof(f1292,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))),
% 1.78/0.58    inference(subsumption_resolution,[],[f1282,f50])).
% 1.78/0.58  fof(f1282,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))),
% 1.78/0.58    inference(resolution,[],[f757,f54])).
% 1.78/0.58  fof(f54,plain,(
% 1.78/0.58    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X1) = k1_xboole_0 | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | v5_pre_topc(X2,X0,X1)) )),
% 1.78/0.58    inference(cnf_transformation,[],[f22])).
% 1.78/0.58  fof(f757,plain,(
% 1.78/0.58    ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(forward_demodulation,[],[f756,f746])).
% 1.78/0.58  fof(f756,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1))) | ~v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f752,f669])).
% 1.78/0.58  fof(f752,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(backward_demodulation,[],[f672,f746])).
% 1.78/0.58  fof(f672,plain,(
% 1.78/0.58    ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(forward_demodulation,[],[f671,f656])).
% 1.78/0.58  fof(f671,plain,(
% 1.78/0.58    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(forward_demodulation,[],[f670,f656])).
% 1.78/0.58  fof(f670,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1))) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(forward_demodulation,[],[f666,f656])).
% 1.78/0.58  fof(f666,plain,(
% 1.78/0.58    ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1))) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(backward_demodulation,[],[f434,f656])).
% 1.78/0.58  fof(f434,plain,(
% 1.78/0.58    ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(forward_demodulation,[],[f430,f427])).
% 1.78/0.58  fof(f430,plain,(
% 1.78/0.58    ~v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(backward_demodulation,[],[f202,f427])).
% 1.78/0.58  fof(f202,plain,(
% 1.78/0.58    ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(forward_demodulation,[],[f185,f184])).
% 1.78/0.58  fof(f185,plain,(
% 1.78/0.58    ~v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(backward_demodulation,[],[f42,f184])).
% 1.78/0.58  fof(f42,plain,(
% 1.78/0.58    ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(cnf_transformation,[],[f18])).
% 1.78/0.58  fof(f1334,plain,(
% 1.78/0.58    m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | k1_xboole_0 != k2_struct_0(sK0)),
% 1.78/0.58    inference(forward_demodulation,[],[f1333,f740])).
% 1.78/0.58  fof(f1333,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | k1_xboole_0 != k2_struct_0(sK0) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))),
% 1.78/0.58    inference(duplicate_literal_removal,[],[f1332])).
% 1.78/0.58  fof(f1332,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v3_pre_topc(sK1,sK0) | k1_xboole_0 != k2_struct_0(sK0) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))),
% 1.78/0.58    inference(forward_demodulation,[],[f1331,f184])).
% 1.78/0.58  fof(f1331,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v3_pre_topc(sK1,sK0) | k1_xboole_0 != k2_struct_0(sK0) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))),
% 1.78/0.58    inference(forward_demodulation,[],[f1330,f740])).
% 1.78/0.58  fof(f1330,plain,(
% 1.78/0.58    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))),
% 1.78/0.58    inference(duplicate_literal_removal,[],[f1329])).
% 1.78/0.58  fof(f1329,plain,(
% 1.78/0.58    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))),
% 1.78/0.58    inference(forward_demodulation,[],[f1328,f184])).
% 1.78/0.58  fof(f1328,plain,(
% 1.78/0.58    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))),
% 1.78/0.58    inference(forward_demodulation,[],[f1327,f740])).
% 1.78/0.58  fof(f1327,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))),
% 1.78/0.58    inference(subsumption_resolution,[],[f1326,f669])).
% 1.78/0.58  fof(f1326,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))),
% 1.78/0.58    inference(subsumption_resolution,[],[f1325,f364])).
% 1.78/0.58  fof(f1325,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))),
% 1.78/0.58    inference(subsumption_resolution,[],[f1285,f50])).
% 1.78/0.58  fof(f1285,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1))))),
% 1.78/0.58    inference(resolution,[],[f757,f58])).
% 1.78/0.58  fof(f58,plain,(
% 1.78/0.58    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X0) != k1_xboole_0 | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | v5_pre_topc(X2,X0,X1)) )),
% 1.78/0.58    inference(cnf_transformation,[],[f22])).
% 1.78/0.58  fof(f2397,plain,(
% 1.78/0.58    ~m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | k1_xboole_0 = k2_struct_0(sK0) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),sK0)),
% 1.78/0.58    inference(forward_demodulation,[],[f2396,f184])).
% 1.78/0.58  fof(f2396,plain,(
% 1.78/0.58    k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f2389,f50])).
% 1.78/0.58  fof(f2389,plain,(
% 1.78/0.58    k1_xboole_0 = k2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),sK0)),
% 1.78/0.58    inference(resolution,[],[f2385,f61])).
% 1.78/0.58  fof(f61,plain,(
% 1.78/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~r2_hidden(X1,u1_pre_topc(X0)) | v3_pre_topc(X1,X0)) )),
% 1.78/0.58    inference(cnf_transformation,[],[f23])).
% 1.78/0.58  fof(f23,plain,(
% 1.78/0.58    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0))),
% 1.78/0.58    inference(ennf_transformation,[],[f4])).
% 1.78/0.58  fof(f4,axiom,(
% 1.78/0.58    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> r2_hidden(X1,u1_pre_topc(X0)))))),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_pre_topc)).
% 1.78/0.58  fof(f2385,plain,(
% 1.78/0.58    r2_hidden(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),u1_pre_topc(sK0)) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.78/0.58    inference(duplicate_literal_removal,[],[f2383])).
% 1.78/0.58  fof(f2383,plain,(
% 1.78/0.58    r2_hidden(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),u1_pre_topc(sK0)) | k1_xboole_0 = k2_struct_0(sK0) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.78/0.58    inference(superposition,[],[f2377,f2208])).
% 1.78/0.58  fof(f2208,plain,(
% 1.78/0.58    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f2203,f188])).
% 1.78/0.58  fof(f2203,plain,(
% 1.78/0.58    k1_xboole_0 = k2_struct_0(sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1) | ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.78/0.58    inference(resolution,[],[f2201,f1688])).
% 1.78/0.58  fof(f1688,plain,(
% 1.78/0.58    ( ! [X1] : (~v3_pre_topc(X1,sK0) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.78/0.58    inference(duplicate_literal_removal,[],[f1687])).
% 1.78/0.58  fof(f1687,plain,(
% 1.78/0.58    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X1,sK0)) )),
% 1.78/0.58    inference(forward_demodulation,[],[f1686,f184])).
% 1.78/0.58  fof(f1686,plain,(
% 1.78/0.58    ( ! [X1] : (u1_pre_topc(sK0) = k5_tmap_1(sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0)) )),
% 1.78/0.58    inference(subsumption_resolution,[],[f1685,f50])).
% 1.78/0.58  fof(f1685,plain,(
% 1.78/0.58    ( ! [X1] : (u1_pre_topc(sK0) = k5_tmap_1(sK0,X1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_pre_topc(X1,sK0)) )),
% 1.78/0.58    inference(resolution,[],[f194,f62])).
% 1.78/0.58  fof(f62,plain,(
% 1.78/0.58    ( ! [X0,X1] : (~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | r2_hidden(X1,u1_pre_topc(X0)) | ~v3_pre_topc(X1,X0)) )),
% 1.78/0.58    inference(cnf_transformation,[],[f23])).
% 1.78/0.58  fof(f194,plain,(
% 1.78/0.58    ( ! [X4] : (~r2_hidden(X4,u1_pre_topc(sK0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.78/0.58    inference(backward_demodulation,[],[f114,f184])).
% 1.78/0.58  fof(f114,plain,(
% 1.78/0.58    ( ! [X4] : (~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X4) | ~r2_hidden(X4,u1_pre_topc(sK0))) )),
% 1.78/0.58    inference(subsumption_resolution,[],[f113,f50])).
% 1.78/0.58  fof(f113,plain,(
% 1.78/0.58    ( ! [X4] : (~l1_pre_topc(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X4) | ~r2_hidden(X4,u1_pre_topc(sK0))) )),
% 1.78/0.58    inference(subsumption_resolution,[],[f91,f49])).
% 1.78/0.58  fof(f91,plain,(
% 1.78/0.58    ( ! [X4] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X4,k1_zfmisc_1(u1_struct_0(sK0))) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X4) | ~r2_hidden(X4,u1_pre_topc(sK0))) )),
% 1.78/0.58    inference(resolution,[],[f48,f70])).
% 1.78/0.58  fof(f70,plain,(
% 1.78/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | u1_pre_topc(X0) = k5_tmap_1(X0,X1) | ~r2_hidden(X1,u1_pre_topc(X0))) )),
% 1.78/0.58    inference(cnf_transformation,[],[f31])).
% 1.78/0.58  fof(f31,plain,(
% 1.78/0.58    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 1.78/0.58    inference(flattening,[],[f30])).
% 1.78/0.58  fof(f30,plain,(
% 1.78/0.58    ! [X0] : (! [X1] : ((r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 1.78/0.58    inference(ennf_transformation,[],[f12])).
% 1.78/0.58  fof(f12,axiom,(
% 1.78/0.58    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (r2_hidden(X1,u1_pre_topc(X0)) <=> u1_pre_topc(X0) = k5_tmap_1(X0,X1))))),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_tmap_1)).
% 1.78/0.58  fof(f2377,plain,(
% 1.78/0.58    r2_hidden(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k5_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f2368,f2256])).
% 1.78/0.58  fof(f2368,plain,(
% 1.78/0.58    k1_xboole_0 = k2_struct_0(sK0) | r2_hidden(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k5_tmap_1(sK0,sK1)) | ~m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))),
% 1.78/0.58    inference(resolution,[],[f2358,f1463])).
% 1.78/0.58  fof(f1463,plain,(
% 1.78/0.58    ( ! [X3] : (~v3_pre_topc(X3,k6_tmap_1(sK0,sK1)) | r2_hidden(X3,k5_tmap_1(sK0,sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_struct_0(sK0)))) )),
% 1.78/0.58    inference(forward_demodulation,[],[f1462,f740])).
% 1.78/0.58  fof(f1462,plain,(
% 1.78/0.58    ( ! [X3] : (r2_hidden(X3,k5_tmap_1(sK0,sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X3,k6_tmap_1(sK0,sK1))) )),
% 1.78/0.58    inference(subsumption_resolution,[],[f1459,f364])).
% 1.78/0.58  fof(f1459,plain,(
% 1.78/0.58    ( ! [X3] : (r2_hidden(X3,k5_tmap_1(sK0,sK1)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X3,k6_tmap_1(sK0,sK1))) )),
% 1.78/0.58    inference(superposition,[],[f62,f1446])).
% 1.78/0.58  fof(f1446,plain,(
% 1.78/0.58    u1_pre_topc(k6_tmap_1(sK0,sK1)) = k5_tmap_1(sK0,sK1)),
% 1.78/0.58    inference(resolution,[],[f192,f188])).
% 1.78/0.58  fof(f192,plain,(
% 1.78/0.58    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_struct_0(sK0))) | k5_tmap_1(sK0,X2) = u1_pre_topc(k6_tmap_1(sK0,X2))) )),
% 1.78/0.58    inference(backward_demodulation,[],[f110,f184])).
% 1.78/0.58  fof(f110,plain,(
% 1.78/0.58    ( ! [X2] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k5_tmap_1(sK0,X2) = u1_pre_topc(k6_tmap_1(sK0,X2))) )),
% 1.78/0.58    inference(subsumption_resolution,[],[f109,f50])).
% 1.78/0.58  fof(f109,plain,(
% 1.78/0.58    ( ! [X2] : (~l1_pre_topc(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k5_tmap_1(sK0,X2) = u1_pre_topc(k6_tmap_1(sK0,X2))) )),
% 1.78/0.58    inference(subsumption_resolution,[],[f89,f49])).
% 1.78/0.58  fof(f89,plain,(
% 1.78/0.58    ( ! [X2] : (~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(sK0))) | k5_tmap_1(sK0,X2) = u1_pre_topc(k6_tmap_1(sK0,X2))) )),
% 1.78/0.58    inference(resolution,[],[f48,f68])).
% 1.78/0.58  fof(f68,plain,(
% 1.78/0.58    ( ! [X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | k5_tmap_1(X0,X1) = u1_pre_topc(k6_tmap_1(X0,X1))) )),
% 1.78/0.58    inference(cnf_transformation,[],[f29])).
% 1.78/0.58  fof(f2358,plain,(
% 1.78/0.58    v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.78/0.58    inference(resolution,[],[f2357,f2201])).
% 1.78/0.58  fof(f2357,plain,(
% 1.78/0.58    ~v3_pre_topc(sK1,sK0) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(subsumption_resolution,[],[f2351,f1907])).
% 1.78/0.58  fof(f2351,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v3_pre_topc(sK1,sK0) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(resolution,[],[f1345,f1801])).
% 1.78/0.58  fof(f1345,plain,(
% 1.78/0.58    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v3_pre_topc(sK1,sK0) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(duplicate_literal_removal,[],[f1344])).
% 1.78/0.58  fof(f1344,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v3_pre_topc(sK1,sK0) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(forward_demodulation,[],[f1343,f184])).
% 1.78/0.58  fof(f1343,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v3_pre_topc(sK1,sK0) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(forward_demodulation,[],[f1342,f740])).
% 1.78/0.58  fof(f1342,plain,(
% 1.78/0.58    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(duplicate_literal_removal,[],[f1341])).
% 1.78/0.58  fof(f1341,plain,(
% 1.78/0.58    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(forward_demodulation,[],[f1340,f184])).
% 1.78/0.58  fof(f1340,plain,(
% 1.78/0.58    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(forward_demodulation,[],[f1339,f740])).
% 1.78/0.58  fof(f1339,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(subsumption_resolution,[],[f1338,f1312])).
% 1.78/0.58  fof(f1312,plain,(
% 1.78/0.58    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | k1_xboole_0 = k2_struct_0(sK0) | ~v3_pre_topc(sK1,sK0) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(forward_demodulation,[],[f1311,f746])).
% 1.78/0.58  fof(f1311,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(duplicate_literal_removal,[],[f1310])).
% 1.78/0.58  fof(f1310,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v3_pre_topc(sK1,sK0) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(forward_demodulation,[],[f1309,f184])).
% 1.78/0.58  fof(f1309,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v3_pre_topc(sK1,sK0) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(forward_demodulation,[],[f1308,f740])).
% 1.78/0.58  fof(f1308,plain,(
% 1.78/0.58    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(duplicate_literal_removal,[],[f1307])).
% 1.78/0.58  fof(f1307,plain,(
% 1.78/0.58    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(forward_demodulation,[],[f1306,f184])).
% 1.78/0.58  fof(f1306,plain,(
% 1.78/0.58    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(forward_demodulation,[],[f1305,f740])).
% 1.78/0.58  fof(f1305,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(subsumption_resolution,[],[f1304,f669])).
% 1.78/0.58  fof(f1304,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(subsumption_resolution,[],[f1303,f364])).
% 1.78/0.58  fof(f1303,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(subsumption_resolution,[],[f1283,f50])).
% 1.78/0.58  fof(f1283,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(resolution,[],[f757,f55])).
% 1.78/0.58  fof(f55,plain,(
% 1.78/0.58    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X1) = k1_xboole_0 | v3_pre_topc(sK2(X0,X1,X2),X1) | v5_pre_topc(X2,X0,X1)) )),
% 1.78/0.58    inference(cnf_transformation,[],[f22])).
% 1.78/0.58  fof(f1338,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(subsumption_resolution,[],[f1337,f669])).
% 1.78/0.58  fof(f1337,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(subsumption_resolution,[],[f1336,f364])).
% 1.78/0.58  fof(f1336,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(subsumption_resolution,[],[f1286,f50])).
% 1.78/0.58  fof(f1286,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))),
% 1.78/0.58    inference(resolution,[],[f757,f59])).
% 1.78/0.58  fof(f59,plain,(
% 1.78/0.58    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X0) != k1_xboole_0 | v3_pre_topc(sK2(X0,X1,X2),X1) | v5_pre_topc(X2,X0,X1)) )),
% 1.78/0.58    inference(cnf_transformation,[],[f22])).
% 1.78/0.58  fof(f4169,plain,(
% 1.78/0.58    ~v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),sK0) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f4168,f2201])).
% 1.78/0.58  fof(f4168,plain,(
% 1.78/0.58    ~v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),sK0) | ~v3_pre_topc(sK1,sK0) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.78/0.58    inference(superposition,[],[f1944,f3977])).
% 1.78/0.58  fof(f3977,plain,(
% 1.78/0.58    sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.78/0.58    inference(superposition,[],[f2268,f1934])).
% 1.78/0.58  fof(f2268,plain,(
% 1.78/0.58    sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))) | k1_xboole_0 = k2_struct_0(sK0)),
% 1.78/0.58    inference(resolution,[],[f2256,f75])).
% 1.78/0.58  fof(f75,plain,(
% 1.78/0.58    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1) )),
% 1.78/0.58    inference(cnf_transformation,[],[f36])).
% 1.78/0.58  fof(f36,plain,(
% 1.78/0.58    ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 1.78/0.58    inference(ennf_transformation,[],[f2])).
% 1.78/0.58  fof(f2,axiom,(
% 1.78/0.58    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 1.78/0.58    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t171_funct_2)).
% 1.78/0.58  fof(f1944,plain,(
% 1.78/0.58    ~v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) | ~v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f1943,f1801])).
% 1.78/0.58  fof(f1943,plain,(
% 1.78/0.58    ~v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f1941,f1907])).
% 1.78/0.58  fof(f1941,plain,(
% 1.78/0.58    ~v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(backward_demodulation,[],[f1357,f1934])).
% 1.78/0.58  fof(f1357,plain,(
% 1.78/0.58    ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(subsumption_resolution,[],[f1356,f1324])).
% 1.78/0.58  fof(f1324,plain,(
% 1.78/0.58    ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) | k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(forward_demodulation,[],[f1323,f184])).
% 1.78/0.58  fof(f1323,plain,(
% 1.78/0.58    ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) | k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0)),
% 1.78/0.58    inference(forward_demodulation,[],[f1322,f740])).
% 1.78/0.58  fof(f1322,plain,(
% 1.78/0.58    k1_xboole_0 = k2_struct_0(sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)),
% 1.78/0.58    inference(forward_demodulation,[],[f1321,f746])).
% 1.78/0.58  fof(f1321,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)),
% 1.78/0.58    inference(duplicate_literal_removal,[],[f1320])).
% 1.78/0.58  fof(f1320,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v3_pre_topc(sK1,sK0) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)),
% 1.78/0.58    inference(forward_demodulation,[],[f1319,f184])).
% 1.78/0.58  fof(f1319,plain,(
% 1.78/0.58    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v3_pre_topc(sK1,sK0) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)),
% 1.78/0.58    inference(forward_demodulation,[],[f1318,f740])).
% 1.78/0.58  fof(f1318,plain,(
% 1.78/0.58    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)),
% 1.78/0.58    inference(duplicate_literal_removal,[],[f1317])).
% 1.78/0.58  fof(f1317,plain,(
% 1.78/0.58    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)),
% 1.78/0.58    inference(forward_demodulation,[],[f1316,f184])).
% 1.78/0.58  fof(f1316,plain,(
% 1.78/0.58    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)),
% 1.78/0.58    inference(forward_demodulation,[],[f1315,f740])).
% 1.78/0.59  fof(f1315,plain,(
% 1.78/0.59    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)),
% 1.78/0.59    inference(subsumption_resolution,[],[f1314,f669])).
% 1.78/0.59  fof(f1314,plain,(
% 1.78/0.59    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)),
% 1.78/0.59    inference(subsumption_resolution,[],[f1313,f364])).
% 1.78/0.59  fof(f1313,plain,(
% 1.78/0.59    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)),
% 1.78/0.59    inference(subsumption_resolution,[],[f1284,f50])).
% 1.78/0.59  fof(f1284,plain,(
% 1.78/0.59    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)),
% 1.78/0.59    inference(resolution,[],[f757,f56])).
% 1.78/0.59  fof(f56,plain,(
% 1.78/0.59    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X1) = k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) | v5_pre_topc(X2,X0,X1)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f22])).
% 1.78/0.59  fof(f1356,plain,(
% 1.78/0.59    ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | k1_xboole_0 != k2_struct_0(sK0)),
% 1.78/0.59    inference(forward_demodulation,[],[f1355,f184])).
% 1.78/0.59  fof(f1355,plain,(
% 1.78/0.59    ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | k1_xboole_0 != k2_struct_0(sK0)),
% 1.78/0.59    inference(forward_demodulation,[],[f1354,f740])).
% 1.78/0.59  fof(f1354,plain,(
% 1.78/0.59    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | k1_xboole_0 != k2_struct_0(sK0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)),
% 1.78/0.59    inference(duplicate_literal_removal,[],[f1353])).
% 1.78/0.59  fof(f1353,plain,(
% 1.78/0.59    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v3_pre_topc(sK1,sK0) | k1_xboole_0 != k2_struct_0(sK0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)),
% 1.78/0.59    inference(forward_demodulation,[],[f1352,f184])).
% 1.78/0.59  fof(f1352,plain,(
% 1.78/0.59    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v3_pre_topc(sK1,sK0) | k1_xboole_0 != k2_struct_0(sK0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)),
% 1.78/0.59    inference(forward_demodulation,[],[f1351,f740])).
% 1.78/0.59  fof(f1351,plain,(
% 1.78/0.59    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)),
% 1.78/0.59    inference(duplicate_literal_removal,[],[f1350])).
% 1.78/0.59  fof(f1350,plain,(
% 1.78/0.59    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)),
% 1.78/0.59    inference(forward_demodulation,[],[f1349,f184])).
% 1.78/0.59  fof(f1349,plain,(
% 1.78/0.59    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)),
% 1.78/0.59    inference(forward_demodulation,[],[f1348,f740])).
% 1.78/0.59  fof(f1348,plain,(
% 1.78/0.59    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)),
% 1.78/0.59    inference(subsumption_resolution,[],[f1347,f669])).
% 1.78/0.59  fof(f1347,plain,(
% 1.78/0.59    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)),
% 1.78/0.59    inference(subsumption_resolution,[],[f1346,f364])).
% 1.78/0.59  fof(f1346,plain,(
% 1.78/0.59    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)),
% 1.78/0.59    inference(subsumption_resolution,[],[f1287,f50])).
% 1.78/0.59  fof(f1287,plain,(
% 1.78/0.59    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),sK0)),
% 1.78/0.59    inference(resolution,[],[f757,f60])).
% 1.78/0.59  fof(f60,plain,(
% 1.78/0.59    ( ! [X2,X0,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X0) != k1_xboole_0 | ~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) | v5_pre_topc(X2,X0,X1)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f22])).
% 1.78/0.59  fof(f218,plain,(
% 1.78/0.59    sK1 = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1)),
% 1.78/0.59    inference(resolution,[],[f188,f75])).
% 1.78/0.59  fof(f4326,plain,(
% 1.78/0.59    v3_pre_topc(sK1,sK0) | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),sK0)),
% 1.78/0.59    inference(subsumption_resolution,[],[f4311,f4172])).
% 1.78/0.59  fof(f4172,plain,(
% 1.78/0.59    m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0))),
% 1.78/0.59    inference(backward_demodulation,[],[f188,f4170])).
% 1.78/0.59  fof(f4311,plain,(
% 1.78/0.59    ~m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | v3_pre_topc(sK1,sK0) | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),sK0)),
% 1.78/0.59    inference(trivial_inequality_removal,[],[f4256])).
% 1.78/0.59  fof(f4256,plain,(
% 1.78/0.59    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | v3_pre_topc(sK1,sK0) | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),sK0)),
% 1.78/0.59    inference(backward_demodulation,[],[f2078,f4170])).
% 1.78/0.59  fof(f2078,plain,(
% 1.78/0.59    ~m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | v3_pre_topc(sK1,sK0) | k1_xboole_0 != k2_struct_0(sK0) | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK1),sK0)),
% 1.78/0.59    inference(resolution,[],[f759,f1861])).
% 1.78/0.59  fof(f759,plain,(
% 1.78/0.59    ( ! [X1] : (~v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | v3_pre_topc(sK1,sK0) | k1_xboole_0 != k2_struct_0(sK0) | v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X1),sK0)) )),
% 1.78/0.59    inference(inner_rewriting,[],[f758])).
% 1.78/0.59  fof(f758,plain,(
% 1.78/0.59    ( ! [X1] : (v3_pre_topc(k8_relset_1(k1_xboole_0,k2_struct_0(sK0),k6_partfun1(k1_xboole_0),X1),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(sK1,sK0) | k1_xboole_0 != k2_struct_0(sK0) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1))) )),
% 1.78/0.59    inference(forward_demodulation,[],[f753,f746])).
% 1.78/0.59  fof(f753,plain,(
% 1.78/0.59    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(k8_relset_1(k1_xboole_0,k2_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),X1),sK0) | v3_pre_topc(sK1,sK0) | k1_xboole_0 != k2_struct_0(sK0) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1))) )),
% 1.78/0.59    inference(backward_demodulation,[],[f673,f746])).
% 1.78/0.59  fof(f673,plain,(
% 1.78/0.59    ( ! [X1] : (v3_pre_topc(k8_relset_1(k1_xboole_0,k2_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),X1),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK0,sK1)))) | v3_pre_topc(sK1,sK0) | k1_xboole_0 != k2_struct_0(sK0) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1))) )),
% 1.78/0.59    inference(inner_rewriting,[],[f668])).
% 1.78/0.59  fof(f668,plain,(
% 1.78/0.59    ( ! [X1] : (v3_pre_topc(k8_relset_1(k1_xboole_0,k2_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k2_struct_0(sK0)),X1),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK0,sK1)))) | v3_pre_topc(sK1,sK0) | k1_xboole_0 != k2_struct_0(sK0) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1))) )),
% 1.78/0.59    inference(backward_demodulation,[],[f437,f656])).
% 1.78/0.59  fof(f437,plain,(
% 1.78/0.59    ( ! [X1] : (v3_pre_topc(k8_relset_1(k1_xboole_0,k2_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X1),sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK0,sK1)))) | v3_pre_topc(sK1,sK0) | k1_xboole_0 != k2_struct_0(sK0) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1))) )),
% 1.78/0.59    inference(forward_demodulation,[],[f433,f427])).
% 1.78/0.59  fof(f433,plain,(
% 1.78/0.59    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_struct_0(k6_tmap_1(sK0,sK1)))) | v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X1),sK0) | v3_pre_topc(sK1,sK0) | k1_xboole_0 != k2_struct_0(sK0) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1))) )),
% 1.78/0.59    inference(backward_demodulation,[],[f426,f427])).
% 1.78/0.59  fof(f426,plain,(
% 1.78/0.59    ( ! [X1] : (v3_pre_topc(k8_relset_1(k1_xboole_0,u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X1),sK0) | v3_pre_topc(sK1,sK0) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1))) )),
% 1.78/0.59    inference(inner_rewriting,[],[f425])).
% 1.78/0.59  fof(f425,plain,(
% 1.78/0.59    ( ! [X1] : (v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X1),sK0) | v3_pre_topc(sK1,sK0) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1))) )),
% 1.78/0.59    inference(forward_demodulation,[],[f424,f184])).
% 1.78/0.59  fof(f424,plain,(
% 1.78/0.59    ( ! [X1] : (v3_pre_topc(sK1,sK0) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X1),sK0)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f423,f187])).
% 1.78/0.59  fof(f423,plain,(
% 1.78/0.59    ( ! [X1] : (~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | v3_pre_topc(sK1,sK0) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X1),sK0)) )),
% 1.78/0.59    inference(forward_demodulation,[],[f422,f184])).
% 1.78/0.59  fof(f422,plain,(
% 1.78/0.59    ( ! [X1] : (v3_pre_topc(sK1,sK0) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X1),sK0)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f421,f186])).
% 1.78/0.59  fof(f421,plain,(
% 1.78/0.59    ( ! [X1] : (~v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | v3_pre_topc(sK1,sK0) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X1),sK0)) )),
% 1.78/0.59    inference(forward_demodulation,[],[f420,f184])).
% 1.78/0.59  fof(f420,plain,(
% 1.78/0.59    ( ! [X1] : (v3_pre_topc(sK1,sK0) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X1),sK0)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f419,f43])).
% 1.78/0.59  fof(f419,plain,(
% 1.78/0.59    ( ! [X1] : (v3_pre_topc(sK1,sK0) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X1),sK0)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f418,f364])).
% 1.78/0.59  fof(f418,plain,(
% 1.78/0.59    ( ! [X1] : (v3_pre_topc(sK1,sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X1),sK0)) )),
% 1.78/0.59    inference(subsumption_resolution,[],[f408,f50])).
% 1.78/0.59  fof(f408,plain,(
% 1.78/0.59    ( ! [X1] : (v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)))) | ~v3_pre_topc(X1,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k7_tmap_1(sK0,sK1),X1),sK0)) )),
% 1.78/0.59    inference(resolution,[],[f45,f57])).
% 1.78/0.59  fof(f57,plain,(
% 1.78/0.59    ( ! [X2,X0,X3,X1] : (~l1_pre_topc(X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X0) != k1_xboole_0 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1) | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v5_pre_topc(X2,X0,X1)) )),
% 1.78/0.59    inference(cnf_transformation,[],[f22])).
% 1.78/0.59  fof(f4260,plain,(
% 1.78/0.59    m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | ~v3_pre_topc(sK1,sK0)),
% 1.78/0.59    inference(backward_demodulation,[],[f2248,f4170])).
% 1.78/0.59  fof(f5249,plain,(
% 1.78/0.59    ~m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0)),
% 1.78/0.59    inference(forward_demodulation,[],[f5248,f4171])).
% 1.78/0.59  fof(f4171,plain,(
% 1.78/0.59    k1_xboole_0 = u1_struct_0(sK0)),
% 1.78/0.59    inference(backward_demodulation,[],[f184,f4170])).
% 1.78/0.59  fof(f5248,plain,(
% 1.78/0.59    ~m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0)),
% 1.78/0.59    inference(subsumption_resolution,[],[f5243,f50])).
% 1.78/0.59  fof(f5243,plain,(
% 1.78/0.59    ~l1_pre_topc(sK0) | ~m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0)),
% 1.78/0.59    inference(resolution,[],[f5239,f61])).
% 1.78/0.59  fof(f5239,plain,(
% 1.78/0.59    r2_hidden(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),u1_pre_topc(sK0))),
% 1.78/0.59    inference(subsumption_resolution,[],[f5230,f4329])).
% 1.78/0.59  fof(f5230,plain,(
% 1.78/0.59    ~m1_subset_1(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k1_zfmisc_1(k1_xboole_0)) | r2_hidden(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),u1_pre_topc(sK0))),
% 1.78/0.59    inference(resolution,[],[f5113,f4330])).
% 1.78/0.59  fof(f4330,plain,(
% 1.78/0.59    v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k6_tmap_1(sK0,sK1))),
% 1.78/0.59    inference(subsumption_resolution,[],[f4261,f4328])).
% 1.78/0.59  fof(f4261,plain,(
% 1.78/0.59    v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 1.78/0.59    inference(backward_demodulation,[],[f2357,f4170])).
% 1.78/0.59  fof(f5113,plain,(
% 1.78/0.59    ( ! [X3] : (~v3_pre_topc(X3,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | r2_hidden(X3,u1_pre_topc(sK0))) )),
% 1.78/0.59    inference(backward_demodulation,[],[f4226,f5107])).
% 1.78/0.59  fof(f5107,plain,(
% 1.78/0.59    u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 1.78/0.59    inference(subsumption_resolution,[],[f5099,f4172])).
% 1.78/0.59  fof(f5099,plain,(
% 1.78/0.59    ~m1_subset_1(sK1,k1_zfmisc_1(k1_xboole_0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,sK1)),
% 1.78/0.59    inference(resolution,[],[f4231,f4328])).
% 1.78/0.59  fof(f4231,plain,(
% 1.78/0.59    ( ! [X1] : (~v3_pre_topc(X1,sK0) | ~m1_subset_1(X1,k1_zfmisc_1(k1_xboole_0)) | u1_pre_topc(sK0) = k5_tmap_1(sK0,X1)) )),
% 1.78/0.59    inference(backward_demodulation,[],[f1688,f4170])).
% 1.78/0.59  fof(f4226,plain,(
% 1.78/0.59    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | ~v3_pre_topc(X3,k6_tmap_1(sK0,sK1)) | r2_hidden(X3,k5_tmap_1(sK0,sK1))) )),
% 1.78/0.59    inference(backward_demodulation,[],[f1463,f4170])).
% 1.78/0.59  fof(f5860,plain,(
% 1.78/0.59    ~v3_pre_topc(sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)),sK0)),
% 1.78/0.59    inference(backward_demodulation,[],[f4725,f5856])).
% 1.78/0.59  fof(f5856,plain,(
% 1.78/0.59    sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)) = k10_relat_1(k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)))),
% 1.78/0.59    inference(superposition,[],[f4737,f4242])).
% 1.78/0.59  fof(f4242,plain,(
% 1.78/0.59    ( ! [X0] : (k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),X0) = k10_relat_1(k6_partfun1(k1_xboole_0),X0)) )),
% 1.78/0.59    inference(backward_demodulation,[],[f1934,f4170])).
% 1.78/0.59  fof(f4737,plain,(
% 1.78/0.59    sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)) = k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0)))),
% 1.78/0.59    inference(resolution,[],[f4329,f75])).
% 1.78/0.59  fof(f4725,plain,(
% 1.78/0.59    ~v3_pre_topc(k10_relat_1(k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0)),
% 1.78/0.59    inference(forward_demodulation,[],[f4724,f4242])).
% 1.78/0.59  fof(f4724,plain,(
% 1.78/0.59    ~v3_pre_topc(k8_relset_1(k1_xboole_0,k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0)),
% 1.78/0.59    inference(forward_demodulation,[],[f4723,f4171])).
% 1.78/0.59  fof(f4723,plain,(
% 1.78/0.59    ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),k1_xboole_0,k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0)),
% 1.78/0.59    inference(forward_demodulation,[],[f4722,f4195])).
% 1.78/0.59  fof(f4195,plain,(
% 1.78/0.59    k1_xboole_0 = u1_struct_0(k6_tmap_1(sK0,sK1))),
% 1.78/0.59    inference(backward_demodulation,[],[f740,f4170])).
% 1.78/0.59  fof(f4722,plain,(
% 1.78/0.59    ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0)),
% 1.78/0.59    inference(subsumption_resolution,[],[f4721,f4241])).
% 1.78/0.59  fof(f4241,plain,(
% 1.78/0.59    m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.78/0.59    inference(backward_demodulation,[],[f1907,f4170])).
% 1.78/0.59  fof(f4721,plain,(
% 1.78/0.59    ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0)),
% 1.78/0.59    inference(forward_demodulation,[],[f4720,f4171])).
% 1.78/0.59  fof(f4720,plain,(
% 1.78/0.59    ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k1_xboole_0))) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0)),
% 1.78/0.59    inference(forward_demodulation,[],[f4719,f4195])).
% 1.78/0.59  fof(f4719,plain,(
% 1.78/0.59    ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0)),
% 1.78/0.59    inference(subsumption_resolution,[],[f4718,f4239])).
% 1.78/0.59  fof(f4239,plain,(
% 1.78/0.59    v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0)),
% 1.78/0.59    inference(backward_demodulation,[],[f1801,f4170])).
% 1.78/0.59  fof(f4718,plain,(
% 1.78/0.59    ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0)),
% 1.78/0.59    inference(forward_demodulation,[],[f4717,f4171])).
% 1.78/0.59  fof(f4717,plain,(
% 1.78/0.59    ~v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(sK0),k1_xboole_0) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0)),
% 1.78/0.59    inference(forward_demodulation,[],[f4716,f4195])).
% 1.78/0.59  fof(f4716,plain,(
% 1.78/0.59    ~v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0)),
% 1.78/0.59    inference(subsumption_resolution,[],[f4715,f4170])).
% 1.78/0.59  fof(f4715,plain,(
% 1.78/0.59    ~v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0)),
% 1.78/0.59    inference(subsumption_resolution,[],[f4714,f4194])).
% 1.78/0.59  fof(f4194,plain,(
% 1.78/0.59    v1_funct_1(k6_partfun1(k1_xboole_0))),
% 1.78/0.59    inference(backward_demodulation,[],[f669,f4170])).
% 1.78/0.59  fof(f4714,plain,(
% 1.78/0.59    ~v1_funct_1(k6_partfun1(k1_xboole_0)) | ~v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0)),
% 1.78/0.59    inference(subsumption_resolution,[],[f4713,f364])).
% 1.78/0.59  fof(f4713,plain,(
% 1.78/0.59    ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | ~v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0)),
% 1.78/0.59    inference(subsumption_resolution,[],[f4712,f50])).
% 1.78/0.59  fof(f4712,plain,(
% 1.78/0.59    ~l1_pre_topc(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | ~v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0)),
% 1.78/0.59    inference(subsumption_resolution,[],[f4711,f4328])).
% 1.78/0.59  fof(f4711,plain,(
% 1.78/0.59    ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | ~v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0)),
% 1.78/0.59    inference(subsumption_resolution,[],[f4710,f4241])).
% 1.78/0.59  fof(f4710,plain,(
% 1.78/0.59    ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | ~v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0)),
% 1.78/0.59    inference(subsumption_resolution,[],[f4695,f4239])).
% 1.78/0.59  fof(f4695,plain,(
% 1.78/0.59    ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v3_pre_topc(sK1,sK0) | ~l1_pre_topc(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k1_xboole_0)) | ~v1_funct_2(k6_partfun1(k1_xboole_0),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | k1_xboole_0 != k2_struct_0(sK0) | ~v3_pre_topc(k8_relset_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)),k6_partfun1(k1_xboole_0),sK2(sK0,k6_tmap_1(sK0,sK1),k6_partfun1(k1_xboole_0))),sK0)),
% 1.78/0.59    inference(resolution,[],[f4320,f60])).
% 1.78/0.59  fof(f4320,plain,(
% 1.78/0.59    ~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k1_xboole_0),k1_xboole_0,k1_xboole_0) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v3_pre_topc(sK1,sK0)),
% 1.78/0.59    inference(forward_demodulation,[],[f4319,f4170])).
% 1.78/0.59  fof(f4319,plain,(
% 1.78/0.59    ~v5_pre_topc(k6_partfun1(k1_xboole_0),sK0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0)),
% 1.78/0.59    inference(forward_demodulation,[],[f4202,f4170])).
% 1.78/0.59  fof(f4202,plain,(
% 1.78/0.59    ~m1_subset_1(k6_partfun1(k1_xboole_0),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v3_pre_topc(sK1,sK0)),
% 1.78/0.59    inference(backward_demodulation,[],[f757,f4170])).
% 1.78/0.59  % SZS output end Proof for theBenchmark
% 1.78/0.59  % (30255)------------------------------
% 1.78/0.59  % (30255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.78/0.59  % (30255)Termination reason: Refutation
% 1.78/0.59  
% 1.78/0.59  % (30255)Memory used [KB]: 3070
% 1.78/0.59  % (30255)Time elapsed: 0.167 s
% 1.78/0.59  % (30255)------------------------------
% 1.78/0.59  % (30255)------------------------------
% 1.89/0.59  % (30241)Success in time 0.236 s
%------------------------------------------------------------------------------
