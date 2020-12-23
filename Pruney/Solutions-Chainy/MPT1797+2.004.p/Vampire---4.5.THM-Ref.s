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
% DateTime   : Thu Dec  3 13:19:30 EST 2020

% Result     : Theorem 2.16s
% Output     : Refutation 2.32s
% Verified   : 
% Statistics : Number of formulae       :  230 (22993 expanded)
%              Number of leaves         :   13 (4447 expanded)
%              Depth                    :   45
%              Number of atoms          : 1121 (117624 expanded)
%              Number of equality atoms :  114 (6299 expanded)
%              Maximal formula depth    :   18 (   6 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2438,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2437,f994])).

fof(f994,plain,(
    ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f993,f247])).

fof(f247,plain,
    ( ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f240,f246])).

fof(f246,plain,(
    m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f245,f204])).

fof(f204,plain,(
    k7_tmap_1(sK0,sK1) = k6_partfun1(k2_struct_0(sK0)) ),
    inference(resolution,[],[f143,f99])).

fof(f99,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f52,f95])).

fof(f95,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f91,f56])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f91,plain,(
    l1_struct_0(sK0) ),
    inference(resolution,[],[f57,f55])).

fof(f55,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_tmap_1)).

fof(f57,plain,(
    ! [X0] :
      ( ~ l1_pre_topc(X0)
      | l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f52,plain,(
    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) ),
    inference(cnf_transformation,[],[f20])).

fof(f143,plain,(
    ! [X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_struct_0(sK0)))
      | k6_partfun1(k2_struct_0(sK0)) = k7_tmap_1(sK0,X16) ) ),
    inference(subsumption_resolution,[],[f142,f53])).

fof(f53,plain,(
    ~ v2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f142,plain,(
    ! [X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | k6_partfun1(k2_struct_0(sK0)) = k7_tmap_1(sK0,X16) ) ),
    inference(subsumption_resolution,[],[f141,f55])).

fof(f141,plain,(
    ! [X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | k6_partfun1(k2_struct_0(sK0)) = k7_tmap_1(sK0,X16) ) ),
    inference(subsumption_resolution,[],[f121,f54])).

fof(f54,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f121,plain,(
    ! [X16] :
      ( ~ m1_subset_1(X16,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | k6_partfun1(k2_struct_0(sK0)) = k7_tmap_1(sK0,X16) ) ),
    inference(superposition,[],[f70,f95])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).

fof(f245,plain,(
    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f244,f224])).

fof(f224,plain,(
    u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(sK0) ),
    inference(resolution,[],[f146,f99])).

fof(f146,plain,(
    ! [X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_struct_0(sK0)))
      | k2_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X17)) ) ),
    inference(subsumption_resolution,[],[f145,f53])).

fof(f145,plain,(
    ! [X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | k2_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X17)) ) ),
    inference(subsumption_resolution,[],[f144,f55])).

fof(f144,plain,(
    ! [X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | k2_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X17)) ) ),
    inference(subsumption_resolution,[],[f122,f54])).

fof(f122,plain,(
    ! [X17] :
      ( ~ m1_subset_1(X17,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | k2_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X17)) ) ),
    inference(superposition,[],[f71,f95])).

fof(f71,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
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
         => ( u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1)
            & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).

fof(f244,plain,(
    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) ),
    inference(resolution,[],[f170,f99])).

fof(f170,plain,(
    ! [X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_struct_0(sK0)))
      | m1_subset_1(k7_tmap_1(sK0,X25),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X25))))) ) ),
    inference(subsumption_resolution,[],[f169,f53])).

fof(f169,plain,(
    ! [X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | m1_subset_1(k7_tmap_1(sK0,X25),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X25))))) ) ),
    inference(subsumption_resolution,[],[f168,f55])).

fof(f168,plain,(
    ! [X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | m1_subset_1(k7_tmap_1(sK0,X25),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X25))))) ) ),
    inference(subsumption_resolution,[],[f130,f54])).

fof(f130,plain,(
    ! [X25] :
      ( ~ m1_subset_1(X25,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | m1_subset_1(k7_tmap_1(sK0,X25),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X25))))) ) ),
    inference(superposition,[],[f84,f95])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))
        & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))
        & v1_funct_1(k7_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).

fof(f240,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f231,f239])).

fof(f239,plain,(
    v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f238,f204])).

fof(f238,plain,(
    v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(sK0)) ),
    inference(forward_demodulation,[],[f237,f224])).

fof(f237,plain,(
    v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) ),
    inference(resolution,[],[f167,f99])).

fof(f167,plain,(
    ! [X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_struct_0(sK0)))
      | v1_funct_2(k7_tmap_1(sK0,X24),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X24))) ) ),
    inference(subsumption_resolution,[],[f166,f53])).

fof(f166,plain,(
    ! [X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | v1_funct_2(k7_tmap_1(sK0,X24),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X24))) ) ),
    inference(subsumption_resolution,[],[f165,f55])).

fof(f165,plain,(
    ! [X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | v1_funct_2(k7_tmap_1(sK0,X24),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X24))) ) ),
    inference(subsumption_resolution,[],[f129,f54])).

fof(f129,plain,(
    ! [X24] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | v1_funct_2(k7_tmap_1(sK0,X24),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X24))) ) ),
    inference(superposition,[],[f83,f95])).

fof(f83,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f231,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f229,f224])).

fof(f229,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f214,f224])).

fof(f214,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f213,f204])).

fof(f213,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f212,f204])).

fof(f212,plain,
    ( ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f202,f204])).

fof(f202,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f100,f201])).

fof(f201,plain,(
    v1_funct_1(k7_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f164,f99])).

fof(f164,plain,(
    ! [X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_struct_0(sK0)))
      | v1_funct_1(k7_tmap_1(sK0,X23)) ) ),
    inference(subsumption_resolution,[],[f163,f53])).

fof(f163,plain,(
    ! [X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | v1_funct_1(k7_tmap_1(sK0,X23)) ) ),
    inference(subsumption_resolution,[],[f162,f55])).

fof(f162,plain,(
    ! [X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | v1_funct_1(k7_tmap_1(sK0,X23)) ) ),
    inference(subsumption_resolution,[],[f128,f54])).

fof(f128,plain,(
    ! [X23] :
      ( ~ m1_subset_1(X23,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | v1_funct_1(k7_tmap_1(sK0,X23)) ) ),
    inference(superposition,[],[f82,f95])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v1_funct_1(k7_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f100,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(forward_demodulation,[],[f96,f95])).

fof(f96,plain,
    ( ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f47,f95])).

fof(f47,plain,
    ( ~ v1_funct_1(k7_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))
    | ~ v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))
    | ~ v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f993,plain,
    ( v3_pre_topc(sK1,sK0)
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f992,f516])).

fof(f516,plain,(
    sK1 = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK1) ),
    inference(superposition,[],[f483,f104])).

fof(f104,plain,(
    sK1 = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1) ),
    inference(resolution,[],[f79,f99])).

fof(f79,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X1,k1_zfmisc_1(X0))
     => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).

fof(f483,plain,(
    ! [X0] : k10_relat_1(k6_partfun1(k2_struct_0(sK0)),X0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),X0) ),
    inference(resolution,[],[f246,f85])).

fof(f85,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f992,plain,
    ( v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK1),sK0)
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f990,f99])).

fof(f990,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK1),sK0)
    | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f627,f344])).

fof(f344,plain,(
    v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f343,f99])).

fof(f343,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f342,f95])).

fof(f342,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f341,f53])).

fof(f341,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f340,f55])).

fof(f340,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f339,f54])).

fof(f339,plain,
    ( ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f287,f99])).

fof(f287,plain,
    ( ~ m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))
    | v2_struct_0(sK0)
    | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1)) ),
    inference(superposition,[],[f86,f224])).

fof(f86,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2))))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
      | v2_struct_0(X0)
      | v3_pre_topc(X2,k6_tmap_1(X0,X2)) ) ),
    inference(equality_resolution,[],[f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))
      | X1 != X2
      | v3_pre_topc(X2,k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
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
    inference(flattening,[],[f35])).

fof(f35,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tmap_1)).

fof(f627,plain,(
    ! [X0] :
      ( ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),X0),sK0)
      | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f626,f483])).

fof(f626,plain,(
    ! [X0] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1))
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),X0),sK0)
      | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f625,f239])).

fof(f625,plain,(
    ! [X0] :
      ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1))
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),X0),sK0)
      | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f623,f211])).

fof(f211,plain,(
    v1_funct_1(k6_partfun1(k2_struct_0(sK0))) ),
    inference(backward_demodulation,[],[f201,f204])).

fof(f623,plain,(
    ! [X0] :
      ( ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
      | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X0,k6_tmap_1(sK0,sK1))
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),X0),sK0)
      | ~ v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(resolution,[],[f433,f246])).

fof(f433,plain,(
    ! [X70,X71] :
      ( ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_1(X70)
      | ~ v1_funct_2(X70,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X71,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X71,k6_tmap_1(sK0,sK1))
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X70,X71),sK0)
      | ~ v5_pre_topc(X70,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f432,f430])).

fof(f430,plain,(
    ! [X66,X67] :
      ( ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | k1_xboole_0 = k2_struct_0(sK0)
      | ~ v1_funct_1(X66)
      | ~ v1_funct_2(X66,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X67,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X67,k6_tmap_1(sK0,sK1))
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X66,X67),sK0)
      | ~ v5_pre_topc(X66,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f429,f259])).

fof(f259,plain,(
    k2_struct_0(sK0) = k2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(forward_demodulation,[],[f258,f224])).

fof(f258,plain,(
    u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f232,f56])).

fof(f232,plain,(
    l1_struct_0(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f200,f57])).

fof(f200,plain,(
    l1_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f161,f99])).

fof(f161,plain,(
    ! [X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_struct_0(sK0)))
      | l1_pre_topc(k6_tmap_1(sK0,X22)) ) ),
    inference(subsumption_resolution,[],[f160,f53])).

fof(f160,plain,(
    ! [X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | l1_pre_topc(k6_tmap_1(sK0,X22)) ) ),
    inference(subsumption_resolution,[],[f159,f55])).

fof(f159,plain,(
    ! [X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | l1_pre_topc(k6_tmap_1(sK0,X22)) ) ),
    inference(subsumption_resolution,[],[f127,f54])).

fof(f127,plain,(
    ! [X22] :
      ( ~ m1_subset_1(X22,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | l1_pre_topc(k6_tmap_1(sK0,X22)) ) ),
    inference(superposition,[],[f81,f95])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | l1_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) )
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ( l1_pre_topc(k6_tmap_1(X0,X1))
        & v2_pre_topc(k6_tmap_1(X0,X1))
        & v1_pre_topc(k6_tmap_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).

fof(f429,plain,(
    ! [X66,X67] :
      ( ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_1(X66)
      | ~ v1_funct_2(X66,k2_struct_0(sK0),k2_struct_0(sK0))
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X67,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X67,k6_tmap_1(sK0,sK1))
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X66,X67),sK0)
      | ~ v5_pre_topc(X66,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f331,f200])).

fof(f331,plain,(
    ! [X66,X67] :
      ( ~ m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X66)
      | ~ v1_funct_2(X66,k2_struct_0(sK0),k2_struct_0(sK0))
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | ~ m1_subset_1(X67,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X67,k6_tmap_1(sK0,sK1))
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X66,X67),sK0)
      | ~ v5_pre_topc(X66,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(superposition,[],[f181,f224])).

fof(f181,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1))
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X2,X1)
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X1),X0,X2),sK0)
      | ~ v5_pre_topc(X0,sK0,X1) ) ),
    inference(subsumption_resolution,[],[f179,f55])).

fof(f179,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1))
      | ~ l1_pre_topc(sK0)
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X2,X1)
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X1),X0,X2),sK0)
      | ~ v5_pre_topc(X0,sK0,X1) ) ),
    inference(superposition,[],[f58,f95])).

fof(f58,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | k2_struct_0(X1) = k1_xboole_0
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
      | ~ v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).

fof(f432,plain,(
    ! [X70,X71] :
      ( ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_1(X70)
      | ~ v1_funct_2(X70,k2_struct_0(sK0),k2_struct_0(sK0))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X71,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X71,k6_tmap_1(sK0,sK1))
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X70,X71),sK0)
      | ~ v5_pre_topc(X70,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f333,f200])).

fof(f333,plain,(
    ! [X70,X71] :
      ( ~ m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X70)
      | ~ v1_funct_2(X70,k2_struct_0(sK0),k2_struct_0(sK0))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X71,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v3_pre_topc(X71,k6_tmap_1(sK0,sK1))
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X70,X71),sK0)
      | ~ v5_pre_topc(X70,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(superposition,[],[f185,f224])).

fof(f185,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X2,X1)
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X1),X0,X2),sK0)
      | ~ v5_pre_topc(X0,sK0,X1) ) ),
    inference(subsumption_resolution,[],[f183,f55])).

fof(f183,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1))
      | ~ l1_pre_topc(sK0)
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X2,X1)
      | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X1),X0,X2),sK0)
      | ~ v5_pre_topc(X0,sK0,X1) ) ),
    inference(superposition,[],[f62,f95])).

fof(f62,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | k2_struct_0(X0) != k1_xboole_0
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | ~ v3_pre_topc(X3,X1)
      | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0)
      | ~ v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2437,plain,(
    v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2436,f211])).

fof(f2436,plain,
    ( ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2435,f246])).

fof(f2435,plain,
    ( ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2422,f239])).

fof(f2422,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f2418,f1073])).

fof(f1073,plain,(
    ! [X74] :
      ( ~ v5_pre_topc(X74,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
      | ~ v1_funct_2(X74,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_1(X74)
      | v5_pre_topc(X74,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f1072,f1029])).

fof(f1029,plain,(
    k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(subsumption_resolution,[],[f243,f995])).

fof(f995,plain,(
    v3_pre_topc(sK1,sK0) ),
    inference(subsumption_resolution,[],[f206,f994])).

fof(f206,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(backward_demodulation,[],[f50,f204])).

fof(f50,plain,
    ( v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1))
    | v3_pre_topc(sK1,sK0) ),
    inference(cnf_transformation,[],[f20])).

fof(f243,plain,
    ( ~ v3_pre_topc(sK1,sK0)
    | k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) ),
    inference(resolution,[],[f155,f99])).

fof(f155,plain,(
    ! [X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_struct_0(sK0)))
      | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X20)
      | ~ v3_pre_topc(X20,sK0) ) ),
    inference(subsumption_resolution,[],[f154,f53])).

fof(f154,plain,(
    ! [X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X20)
      | ~ v3_pre_topc(X20,sK0) ) ),
    inference(subsumption_resolution,[],[f153,f55])).

fof(f153,plain,(
    ! [X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X20)
      | ~ v3_pre_topc(X20,sK0) ) ),
    inference(subsumption_resolution,[],[f125,f54])).

fof(f125,plain,(
    ! [X20] :
      ( ~ m1_subset_1(X20,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X20)
      | ~ v3_pre_topc(X20,sK0) ) ),
    inference(superposition,[],[f74,f95])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)
      | ~ v3_pre_topc(X1,X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) )
          | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
         => ( v3_pre_topc(X1,X0)
          <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).

fof(f1072,plain,(
    ! [X74] :
      ( ~ v1_funct_2(X74,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_1(X74)
      | ~ v5_pre_topc(X74,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
      | v5_pre_topc(X74,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(duplicate_literal_removal,[],[f1071])).

fof(f1071,plain,(
    ! [X74] :
      ( ~ v1_funct_2(X74,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_1(X74)
      | ~ v1_funct_2(X74,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ v5_pre_topc(X74,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
      | v5_pre_topc(X74,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f1070,f224])).

fof(f1070,plain,(
    ! [X74] :
      ( ~ v1_funct_2(X74,u1_struct_0(k6_tmap_1(sK0,sK1)),k2_struct_0(sK0))
      | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_1(X74)
      | ~ v1_funct_2(X74,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ v5_pre_topc(X74,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
      | v5_pre_topc(X74,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f1069,f1029])).

fof(f1069,plain,(
    ! [X74] :
      ( ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_1(X74)
      | ~ v1_funct_2(X74,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ v1_funct_2(X74,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(sK0))
      | ~ v5_pre_topc(X74,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
      | v5_pre_topc(X74,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(duplicate_literal_removal,[],[f1068])).

fof(f1068,plain,(
    ! [X74] :
      ( ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_1(X74)
      | ~ v1_funct_2(X74,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_2(X74,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(sK0))
      | ~ v5_pre_topc(X74,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
      | v5_pre_topc(X74,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f1037,f224])).

fof(f1037,plain,(
    ! [X74] :
      ( ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),k2_struct_0(sK0))))
      | ~ v1_funct_1(X74)
      | ~ v1_funct_2(X74,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_2(X74,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(sK0))
      | ~ v5_pre_topc(X74,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
      | v5_pre_topc(X74,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(backward_demodulation,[],[f438,f1029])).

fof(f438,plain,(
    ! [X74] :
      ( ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(sK0))))
      | ~ v1_funct_1(X74)
      | ~ v1_funct_2(X74,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_2(X74,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(sK0))
      | ~ v5_pre_topc(X74,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
      | v5_pre_topc(X74,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f437,f200])).

fof(f437,plain,(
    ! [X74] :
      ( ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(sK0))))
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X74)
      | ~ v1_funct_2(X74,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_2(X74,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(sK0))
      | ~ v5_pre_topc(X74,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
      | v5_pre_topc(X74,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f335,f199])).

fof(f199,plain,(
    v2_pre_topc(k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f158,f99])).

fof(f158,plain,(
    ! [X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_pre_topc(k6_tmap_1(sK0,X21)) ) ),
    inference(subsumption_resolution,[],[f157,f53])).

fof(f157,plain,(
    ! [X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_struct_0(sK0)))
      | v2_struct_0(sK0)
      | v2_pre_topc(k6_tmap_1(sK0,X21)) ) ),
    inference(subsumption_resolution,[],[f156,f55])).

fof(f156,plain,(
    ! [X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | v2_pre_topc(k6_tmap_1(sK0,X21)) ) ),
    inference(subsumption_resolution,[],[f126,f54])).

fof(f126,plain,(
    ! [X21] :
      ( ~ m1_subset_1(X21,k1_zfmisc_1(k2_struct_0(sK0)))
      | ~ v2_pre_topc(sK0)
      | ~ l1_pre_topc(sK0)
      | v2_struct_0(sK0)
      | v2_pre_topc(k6_tmap_1(sK0,X21)) ) ),
    inference(superposition,[],[f80,f95])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X0)
      | v2_pre_topc(k6_tmap_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f335,plain,(
    ! [X74] :
      ( ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(sK0))))
      | ~ v2_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X74)
      | ~ v1_funct_2(X74,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_2(X74,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(sK0))
      | ~ v5_pre_topc(X74,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1))
      | v5_pre_topc(X74,sK0,k6_tmap_1(sK0,sK1)) ) ),
    inference(superposition,[],[f190,f224])).

fof(f190,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))))
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))
      | ~ v5_pre_topc(X0,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X1)
      | v5_pre_topc(X0,sK0,X1) ) ),
    inference(subsumption_resolution,[],[f189,f54])).

fof(f189,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))))
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))
      | ~ v2_pre_topc(sK0)
      | ~ v5_pre_topc(X0,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X1)
      | v5_pre_topc(X0,sK0,X1) ) ),
    inference(subsumption_resolution,[],[f187,f55])).

fof(f187,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))))
      | ~ l1_pre_topc(sK0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1))))
      | ~ v1_funct_2(X0,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1))
      | ~ v2_pre_topc(sK0)
      | ~ v5_pre_topc(X0,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X1)
      | v5_pre_topc(X0,sK0,X1) ) ),
    inference(superposition,[],[f89,f95])).

fof(f89,plain,(
    ! [X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))))
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1))
      | ~ v2_pre_topc(X0)
      | ~ v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)
      | v5_pre_topc(X3,X0,X1) ) ),
    inference(duplicate_literal_removal,[],[f88])).

fof(f88,plain,(
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
    inference(equality_resolution,[],[f76])).

fof(f76,plain,(
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
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
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
    inference(flattening,[],[f37])).

fof(f37,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).

fof(f2418,plain,(
    v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2417,f1304])).

fof(f1304,plain,
    ( v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1303,f239])).

fof(f1303,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1301,f211])).

fof(f1301,plain,
    ( ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f590,f246])).

fof(f590,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
      | v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1),k6_tmap_1(sK0,sK1))
      | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f589,f586])).

fof(f586,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | k1_xboole_0 = k2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
      | v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1),k6_tmap_1(sK0,sK1))
      | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f585,f259])).

fof(f585,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1),k6_tmap_1(sK0,sK1))
      | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f584,f200])).

fof(f584,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1),k6_tmap_1(sK0,sK1))
      | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(superposition,[],[f351,f224])).

fof(f351,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X11))))
      | ~ l1_pre_topc(X11)
      | ~ v1_funct_1(X10)
      | ~ v1_funct_2(X10,k2_struct_0(sK0),u1_struct_0(X11))
      | k1_xboole_0 = k2_struct_0(X11)
      | v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),X11,X10),X11)
      | v5_pre_topc(X10,k6_tmap_1(sK0,sK1),X11) ) ),
    inference(subsumption_resolution,[],[f292,f200])).

fof(f292,plain,(
    ! [X10,X11] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X11))))
      | ~ l1_pre_topc(X11)
      | ~ v1_funct_1(X10)
      | ~ v1_funct_2(X10,k2_struct_0(sK0),u1_struct_0(X11))
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | k1_xboole_0 = k2_struct_0(X11)
      | v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),X11,X10),X11)
      | v5_pre_topc(X10,k6_tmap_1(sK0,sK1),X11) ) ),
    inference(superposition,[],[f60,f224])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | k2_struct_0(X1) = k1_xboole_0
      | v3_pre_topc(sK2(X0,X1,X2),X1)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f589,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
      | v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1),k6_tmap_1(sK0,sK1))
      | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f588,f200])).

fof(f588,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
      | v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1),k6_tmap_1(sK0,sK1))
      | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(superposition,[],[f364,f224])).

fof(f364,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X29))))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ l1_pre_topc(X29)
      | ~ v1_funct_1(X28)
      | ~ v1_funct_2(X28,k2_struct_0(sK0),u1_struct_0(X29))
      | v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),X29,X28),X29)
      | v5_pre_topc(X28,k6_tmap_1(sK0,sK1),X29) ) ),
    inference(forward_demodulation,[],[f363,f259])).

fof(f363,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X29))))
      | ~ l1_pre_topc(X29)
      | ~ v1_funct_1(X28)
      | ~ v1_funct_2(X28,k2_struct_0(sK0),u1_struct_0(X29))
      | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1))
      | v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),X29,X28),X29)
      | v5_pre_topc(X28,k6_tmap_1(sK0,sK1),X29) ) ),
    inference(subsumption_resolution,[],[f300,f200])).

fof(f300,plain,(
    ! [X28,X29] :
      ( ~ m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X29))))
      | ~ l1_pre_topc(X29)
      | ~ v1_funct_1(X28)
      | ~ v1_funct_2(X28,k2_struct_0(sK0),u1_struct_0(X29))
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1))
      | v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),X29,X28),X29)
      | v5_pre_topc(X28,k6_tmap_1(sK0,sK1),X29) ) ),
    inference(superposition,[],[f64,f224])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | k2_struct_0(X0) != k1_xboole_0
      | v3_pre_topc(sK2(X0,X1,X2),X1)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f2417,plain,
    ( ~ v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ),
    inference(backward_demodulation,[],[f1316,f2415])).

fof(f2415,plain,(
    sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))) ),
    inference(subsumption_resolution,[],[f2414,f994])).

fof(f2414,plain,
    ( sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2413,f211])).

fof(f2413,plain,
    ( sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2412,f246])).

fof(f2412,plain,
    ( sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f2399,f239])).

fof(f2399,plain,
    ( sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f1737,f1073])).

fof(f1737,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))) ),
    inference(forward_demodulation,[],[f1735,f483])).

fof(f1735,plain,
    ( v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))
    | sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))) ),
    inference(resolution,[],[f1308,f79])).

fof(f1308,plain,
    ( m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1307,f239])).

fof(f1307,plain,
    ( ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1305,f211])).

fof(f1305,plain,
    ( ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0)))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ),
    inference(resolution,[],[f613,f246])).

fof(f613,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1),k1_zfmisc_1(k2_struct_0(sK0)))
      | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f612,f605])).

fof(f605,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | k1_xboole_0 = k2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1),k1_zfmisc_1(k2_struct_0(sK0)))
      | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f604,f259])).

fof(f604,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1),k1_zfmisc_1(k2_struct_0(sK0)))
      | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f603,f200])).

fof(f603,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1),k1_zfmisc_1(k2_struct_0(sK0)))
      | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(superposition,[],[f348,f224])).

fof(f348,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X7))))
      | ~ l1_pre_topc(X7)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k2_struct_0(sK0),u1_struct_0(X7))
      | k1_xboole_0 = k2_struct_0(X7)
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),X7,X6),k1_zfmisc_1(u1_struct_0(X7)))
      | v5_pre_topc(X6,k6_tmap_1(sK0,sK1),X7) ) ),
    inference(subsumption_resolution,[],[f290,f200])).

fof(f290,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X7))))
      | ~ l1_pre_topc(X7)
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,k2_struct_0(sK0),u1_struct_0(X7))
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | k1_xboole_0 = k2_struct_0(X7)
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),X7,X6),k1_zfmisc_1(u1_struct_0(X7)))
      | v5_pre_topc(X6,k6_tmap_1(sK0,sK1),X7) ) ),
    inference(superposition,[],[f59,f224])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | k2_struct_0(X1) = k1_xboole_0
      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f612,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1),k1_zfmisc_1(k2_struct_0(sK0)))
      | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f611,f200])).

fof(f611,plain,(
    ! [X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1),k1_zfmisc_1(k2_struct_0(sK0)))
      | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(superposition,[],[f361,f224])).

fof(f361,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X25))))
      | k1_xboole_0 != k2_struct_0(sK0)
      | ~ l1_pre_topc(X25)
      | ~ v1_funct_1(X24)
      | ~ v1_funct_2(X24,k2_struct_0(sK0),u1_struct_0(X25))
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),X25,X24),k1_zfmisc_1(u1_struct_0(X25)))
      | v5_pre_topc(X24,k6_tmap_1(sK0,sK1),X25) ) ),
    inference(forward_demodulation,[],[f360,f259])).

fof(f360,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X25))))
      | ~ l1_pre_topc(X25)
      | ~ v1_funct_1(X24)
      | ~ v1_funct_2(X24,k2_struct_0(sK0),u1_struct_0(X25))
      | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1))
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),X25,X24),k1_zfmisc_1(u1_struct_0(X25)))
      | v5_pre_topc(X24,k6_tmap_1(sK0,sK1),X25) ) ),
    inference(subsumption_resolution,[],[f298,f200])).

fof(f298,plain,(
    ! [X24,X25] :
      ( ~ m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X25))))
      | ~ l1_pre_topc(X25)
      | ~ v1_funct_1(X24)
      | ~ v1_funct_2(X24,k2_struct_0(sK0),u1_struct_0(X25))
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1))
      | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),X25,X24),k1_zfmisc_1(u1_struct_0(X25)))
      | v5_pre_topc(X24,k6_tmap_1(sK0,sK1),X25) ) ),
    inference(superposition,[],[f63,f224])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ l1_pre_topc(X0)
      | k2_struct_0(X0) != k1_xboole_0
      | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f1316,plain,
    ( ~ v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),k6_tmap_1(sK0,sK1))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1315,f246])).

fof(f1315,plain,
    ( ~ v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),k6_tmap_1(sK0,sK1))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1314,f239])).

fof(f1314,plain,
    ( ~ v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),k6_tmap_1(sK0,sK1))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ),
    inference(subsumption_resolution,[],[f1313,f211])).

fof(f1313,plain,
    ( ~ v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),k6_tmap_1(sK0,sK1))
    | ~ v1_funct_1(k6_partfun1(k2_struct_0(sK0)))
    | ~ v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))
    | ~ m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
    | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ),
    inference(superposition,[],[f647,f483])).

fof(f647,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1)),k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f646,f642])).

fof(f642,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1)),k6_tmap_1(sK0,sK1))
      | k1_xboole_0 = k2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f641,f200])).

fof(f641,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1)),k6_tmap_1(sK0,sK1))
      | k1_xboole_0 = k2_struct_0(sK0)
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(superposition,[],[f356,f224])).

fof(f356,plain,(
    ! [X17,X16] :
      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X16),k2_struct_0(sK0),X17,sK2(X16,k6_tmap_1(sK0,sK1),X17)),X16)
      | k1_xboole_0 = k2_struct_0(sK0)
      | ~ v1_funct_1(X17)
      | ~ v1_funct_2(X17,u1_struct_0(X16),k2_struct_0(sK0))
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),k2_struct_0(sK0))))
      | ~ l1_pre_topc(X16)
      | v5_pre_topc(X17,X16,k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f355,f259])).

fof(f355,plain,(
    ! [X17,X16] :
      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X16),k2_struct_0(sK0),X17,sK2(X16,k6_tmap_1(sK0,sK1),X17)),X16)
      | ~ v1_funct_1(X17)
      | ~ v1_funct_2(X17,u1_struct_0(X16),k2_struct_0(sK0))
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),k2_struct_0(sK0))))
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(X16)
      | v5_pre_topc(X17,X16,k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f295,f200])).

fof(f295,plain,(
    ! [X17,X16] :
      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X16),k2_struct_0(sK0),X17,sK2(X16,k6_tmap_1(sK0,sK1),X17)),X16)
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X17)
      | ~ v1_funct_2(X17,u1_struct_0(X16),k2_struct_0(sK0))
      | ~ m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),k2_struct_0(sK0))))
      | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(X16)
      | v5_pre_topc(X17,X16,k6_tmap_1(sK0,sK1)) ) ),
    inference(superposition,[],[f61,f224])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_struct_0(X1) = k1_xboole_0
      | ~ l1_pre_topc(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f646,plain,(
    ! [X1] :
      ( k1_xboole_0 != k2_struct_0(sK0)
      | ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1)),k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(forward_demodulation,[],[f645,f259])).

fof(f645,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1)),k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1))
      | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f644,f200])).

fof(f644,plain,(
    ! [X1] :
      ( ~ v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1)),k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0))
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))
      | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1))
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) ) ),
    inference(superposition,[],[f368,f224])).

fof(f368,plain,(
    ! [X35,X34] :
      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X34),k2_struct_0(sK0),X35,sK2(X34,k6_tmap_1(sK0,sK1),X35)),X34)
      | ~ v1_funct_1(X35)
      | ~ v1_funct_2(X35,u1_struct_0(X34),k2_struct_0(sK0))
      | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),k2_struct_0(sK0))))
      | k1_xboole_0 != k2_struct_0(X34)
      | ~ l1_pre_topc(X34)
      | v5_pre_topc(X35,X34,k6_tmap_1(sK0,sK1)) ) ),
    inference(subsumption_resolution,[],[f303,f200])).

fof(f303,plain,(
    ! [X35,X34] :
      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X34),k2_struct_0(sK0),X35,sK2(X34,k6_tmap_1(sK0,sK1),X35)),X34)
      | ~ l1_pre_topc(k6_tmap_1(sK0,sK1))
      | ~ v1_funct_1(X35)
      | ~ v1_funct_2(X35,u1_struct_0(X34),k2_struct_0(sK0))
      | ~ m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),k2_struct_0(sK0))))
      | k1_xboole_0 != k2_struct_0(X34)
      | ~ l1_pre_topc(X34)
      | v5_pre_topc(X35,X34,k6_tmap_1(sK0,sK1)) ) ),
    inference(superposition,[],[f65,f224])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_struct_0(X0) != k1_xboole_0
      | ~ l1_pre_topc(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n003.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 14:04:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.47  % (32713)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.22/0.48  % (32726)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.22/0.48  % (32718)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.22/0.49  % (32721)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.22/0.50  % (32709)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.50  % (32722)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.22/0.50  % (32707)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.50  % (32727)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.22/0.50  % (32720)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.22/0.50  % (32725)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.22/0.50  % (32706)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.22/0.50  % (32707)Refutation not found, incomplete strategy% (32707)------------------------------
% 0.22/0.50  % (32707)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.50  % (32707)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.50  
% 0.22/0.50  % (32707)Memory used [KB]: 10618
% 0.22/0.50  % (32707)Time elapsed: 0.091 s
% 0.22/0.50  % (32707)------------------------------
% 0.22/0.50  % (32707)------------------------------
% 0.22/0.50  % (32714)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.22/0.51  % (32712)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.22/0.51  % (32711)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.22/0.51  % (32708)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.22/0.51  % (32715)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.22/0.51  % (32716)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.22/0.52  % (32719)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.52  % (32717)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.22/0.52  % (32717)Refutation not found, incomplete strategy% (32717)------------------------------
% 0.22/0.52  % (32717)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (32717)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (32717)Memory used [KB]: 6140
% 0.22/0.52  % (32717)Time elapsed: 0.105 s
% 0.22/0.52  % (32717)------------------------------
% 0.22/0.52  % (32717)------------------------------
% 0.22/0.52  % (32723)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.22/0.52  % (32719)Refutation not found, incomplete strategy% (32719)------------------------------
% 0.22/0.52  % (32719)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (32719)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (32719)Memory used [KB]: 6140
% 0.22/0.52  % (32719)Time elapsed: 0.107 s
% 0.22/0.52  % (32719)------------------------------
% 0.22/0.52  % (32719)------------------------------
% 0.22/0.52  % (32727)Refutation not found, incomplete strategy% (32727)------------------------------
% 0.22/0.52  % (32727)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (32724)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.22/0.52  % (32706)Refutation not found, incomplete strategy% (32706)------------------------------
% 0.22/0.52  % (32706)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.52  % (32706)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.52  
% 0.22/0.52  % (32706)Memory used [KB]: 6268
% 0.22/0.52  % (32706)Time elapsed: 0.096 s
% 0.22/0.52  % (32706)------------------------------
% 0.22/0.52  % (32706)------------------------------
% 0.22/0.53  % (32727)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.53  
% 0.22/0.53  % (32727)Memory used [KB]: 10618
% 0.22/0.53  % (32727)Time elapsed: 0.106 s
% 0.22/0.53  % (32727)------------------------------
% 0.22/0.53  % (32727)------------------------------
% 2.16/0.64  % (32724)Refutation found. Thanks to Tanya!
% 2.16/0.64  % SZS status Theorem for theBenchmark
% 2.16/0.64  % SZS output start Proof for theBenchmark
% 2.16/0.64  fof(f2438,plain,(
% 2.16/0.64    $false),
% 2.16/0.64    inference(subsumption_resolution,[],[f2437,f994])).
% 2.16/0.64  fof(f994,plain,(
% 2.16/0.64    ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(subsumption_resolution,[],[f993,f247])).
% 2.16/0.64  fof(f247,plain,(
% 2.16/0.64    ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 2.16/0.64    inference(subsumption_resolution,[],[f240,f246])).
% 2.16/0.64  fof(f246,plain,(
% 2.16/0.64    m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))),
% 2.16/0.64    inference(forward_demodulation,[],[f245,f204])).
% 2.16/0.64  fof(f204,plain,(
% 2.16/0.64    k7_tmap_1(sK0,sK1) = k6_partfun1(k2_struct_0(sK0))),
% 2.16/0.64    inference(resolution,[],[f143,f99])).
% 2.16/0.64  fof(f99,plain,(
% 2.16/0.64    m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0)))),
% 2.16/0.64    inference(backward_demodulation,[],[f52,f95])).
% 2.16/0.64  fof(f95,plain,(
% 2.16/0.64    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 2.16/0.64    inference(resolution,[],[f91,f56])).
% 2.16/0.64  fof(f56,plain,(
% 2.16/0.64    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 2.16/0.64    inference(cnf_transformation,[],[f21])).
% 2.16/0.64  fof(f21,plain,(
% 2.16/0.64    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 2.16/0.64    inference(ennf_transformation,[],[f3])).
% 2.16/0.64  fof(f3,axiom,(
% 2.16/0.64    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 2.16/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 2.16/0.64  fof(f91,plain,(
% 2.16/0.64    l1_struct_0(sK0)),
% 2.16/0.64    inference(resolution,[],[f57,f55])).
% 2.16/0.64  fof(f55,plain,(
% 2.16/0.64    l1_pre_topc(sK0)),
% 2.16/0.64    inference(cnf_transformation,[],[f20])).
% 2.16/0.64  fof(f20,plain,(
% 2.16/0.64    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0))),
% 2.16/0.64    inference(flattening,[],[f19])).
% 2.16/0.64  fof(f19,plain,(
% 2.16/0.64    ? [X0] : (? [X1] : ((v3_pre_topc(X1,X0) <~> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1)))) & m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) & (l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)))),
% 2.16/0.64    inference(ennf_transformation,[],[f17])).
% 2.16/0.64  fof(f17,negated_conjecture,(
% 2.16/0.64    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 2.16/0.64    inference(negated_conjecture,[],[f16])).
% 2.16/0.64  fof(f16,conjecture,(
% 2.16/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v5_pre_topc(k7_tmap_1(X0,X1),X0,k6_tmap_1(X0,X1)) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))))),
% 2.16/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_tmap_1)).
% 2.16/0.64  fof(f57,plain,(
% 2.16/0.64    ( ! [X0] : (~l1_pre_topc(X0) | l1_struct_0(X0)) )),
% 2.16/0.64    inference(cnf_transformation,[],[f22])).
% 2.16/0.64  fof(f22,plain,(
% 2.16/0.64    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 2.16/0.64    inference(ennf_transformation,[],[f4])).
% 2.16/0.64  fof(f4,axiom,(
% 2.16/0.64    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 2.16/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 2.16/0.64  fof(f52,plain,(
% 2.16/0.64    m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0)))),
% 2.16/0.64    inference(cnf_transformation,[],[f20])).
% 2.16/0.64  fof(f143,plain,(
% 2.16/0.64    ( ! [X16] : (~m1_subset_1(X16,k1_zfmisc_1(k2_struct_0(sK0))) | k6_partfun1(k2_struct_0(sK0)) = k7_tmap_1(sK0,X16)) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f142,f53])).
% 2.16/0.64  fof(f53,plain,(
% 2.16/0.64    ~v2_struct_0(sK0)),
% 2.16/0.64    inference(cnf_transformation,[],[f20])).
% 2.16/0.64  fof(f142,plain,(
% 2.16/0.64    ( ! [X16] : (~m1_subset_1(X16,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | k6_partfun1(k2_struct_0(sK0)) = k7_tmap_1(sK0,X16)) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f141,f55])).
% 2.16/0.64  fof(f141,plain,(
% 2.16/0.64    ( ! [X16] : (~m1_subset_1(X16,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | k6_partfun1(k2_struct_0(sK0)) = k7_tmap_1(sK0,X16)) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f121,f54])).
% 2.16/0.64  fof(f54,plain,(
% 2.16/0.64    v2_pre_topc(sK0)),
% 2.16/0.64    inference(cnf_transformation,[],[f20])).
% 2.16/0.64  fof(f121,plain,(
% 2.16/0.64    ( ! [X16] : (~m1_subset_1(X16,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | k6_partfun1(k2_struct_0(sK0)) = k7_tmap_1(sK0,X16)) )),
% 2.16/0.64    inference(superposition,[],[f70,f95])).
% 2.16/0.64  fof(f70,plain,(
% 2.16/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))) )),
% 2.16/0.64    inference(cnf_transformation,[],[f30])).
% 2.16/0.64  fof(f30,plain,(
% 2.16/0.64    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.16/0.64    inference(flattening,[],[f29])).
% 2.16/0.64  fof(f29,plain,(
% 2.16/0.64    ! [X0] : (! [X1] : (k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.16/0.64    inference(ennf_transformation,[],[f9])).
% 2.16/0.64  fof(f9,axiom,(
% 2.16/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => k7_tmap_1(X0,X1) = k6_partfun1(u1_struct_0(X0))))),
% 2.16/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_tmap_1)).
% 2.16/0.64  fof(f245,plain,(
% 2.16/0.64    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0))))),
% 2.16/0.64    inference(forward_demodulation,[],[f244,f224])).
% 2.16/0.64  fof(f224,plain,(
% 2.16/0.64    u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(sK0)),
% 2.16/0.64    inference(resolution,[],[f146,f99])).
% 2.16/0.64  fof(f146,plain,(
% 2.16/0.64    ( ! [X17] : (~m1_subset_1(X17,k1_zfmisc_1(k2_struct_0(sK0))) | k2_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X17))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f145,f53])).
% 2.16/0.64  fof(f145,plain,(
% 2.16/0.64    ( ! [X17] : (~m1_subset_1(X17,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | k2_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X17))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f144,f55])).
% 2.16/0.64  fof(f144,plain,(
% 2.16/0.64    ( ! [X17] : (~m1_subset_1(X17,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | k2_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X17))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f122,f54])).
% 2.16/0.64  fof(f122,plain,(
% 2.16/0.64    ( ! [X17] : (~m1_subset_1(X17,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | k2_struct_0(sK0) = u1_struct_0(k6_tmap_1(sK0,X17))) )),
% 2.16/0.64    inference(superposition,[],[f71,f95])).
% 2.16/0.64  fof(f71,plain,(
% 2.16/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) )),
% 2.16/0.64    inference(cnf_transformation,[],[f32])).
% 2.16/0.64  fof(f32,plain,(
% 2.16/0.64    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.16/0.64    inference(flattening,[],[f31])).
% 2.16/0.64  fof(f31,plain,(
% 2.16/0.64    ! [X0] : (! [X1] : ((u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.16/0.64    inference(ennf_transformation,[],[f13])).
% 2.16/0.64  fof(f13,axiom,(
% 2.16/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (u1_pre_topc(k6_tmap_1(X0,X1)) = k5_tmap_1(X0,X1) & u1_struct_0(X0) = u1_struct_0(k6_tmap_1(X0,X1)))))),
% 2.16/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t104_tmap_1)).
% 2.16/0.64  fof(f244,plain,(
% 2.16/0.64    m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))))),
% 2.16/0.64    inference(resolution,[],[f170,f99])).
% 2.16/0.64  fof(f170,plain,(
% 2.16/0.64    ( ! [X25] : (~m1_subset_1(X25,k1_zfmisc_1(k2_struct_0(sK0))) | m1_subset_1(k7_tmap_1(sK0,X25),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X25)))))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f169,f53])).
% 2.16/0.64  fof(f169,plain,(
% 2.16/0.64    ( ! [X25] : (~m1_subset_1(X25,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | m1_subset_1(k7_tmap_1(sK0,X25),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X25)))))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f168,f55])).
% 2.16/0.64  fof(f168,plain,(
% 2.16/0.64    ( ! [X25] : (~m1_subset_1(X25,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(k7_tmap_1(sK0,X25),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X25)))))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f130,f54])).
% 2.16/0.64  fof(f130,plain,(
% 2.16/0.64    ( ! [X25] : (~m1_subset_1(X25,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | m1_subset_1(k7_tmap_1(sK0,X25),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X25)))))) )),
% 2.16/0.64    inference(superposition,[],[f84,f95])).
% 2.16/0.64  fof(f84,plain,(
% 2.16/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))))) )),
% 2.16/0.64    inference(cnf_transformation,[],[f45])).
% 2.16/0.64  fof(f45,plain,(
% 2.16/0.64    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.16/0.64    inference(flattening,[],[f44])).
% 2.16/0.64  fof(f44,plain,(
% 2.16/0.64    ! [X0,X1] : ((m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.16/0.64    inference(ennf_transformation,[],[f11])).
% 2.16/0.64  fof(f11,axiom,(
% 2.16/0.64    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (m1_subset_1(k7_tmap_1(X0,X1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))))) & v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1))) & v1_funct_1(k7_tmap_1(X0,X1))))),
% 2.16/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k7_tmap_1)).
% 2.16/0.64  fof(f240,plain,(
% 2.16/0.64    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 2.16/0.64    inference(subsumption_resolution,[],[f231,f239])).
% 2.16/0.64  fof(f239,plain,(
% 2.16/0.64    v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0))),
% 2.16/0.64    inference(forward_demodulation,[],[f238,f204])).
% 2.16/0.64  fof(f238,plain,(
% 2.16/0.64    v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),k2_struct_0(sK0))),
% 2.16/0.64    inference(forward_demodulation,[],[f237,f224])).
% 2.16/0.64  fof(f237,plain,(
% 2.16/0.64    v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1)))),
% 2.16/0.64    inference(resolution,[],[f167,f99])).
% 2.16/0.64  fof(f167,plain,(
% 2.16/0.64    ( ! [X24] : (~m1_subset_1(X24,k1_zfmisc_1(k2_struct_0(sK0))) | v1_funct_2(k7_tmap_1(sK0,X24),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X24)))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f166,f53])).
% 2.16/0.64  fof(f166,plain,(
% 2.16/0.64    ( ! [X24] : (~m1_subset_1(X24,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | v1_funct_2(k7_tmap_1(sK0,X24),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X24)))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f165,f55])).
% 2.16/0.64  fof(f165,plain,(
% 2.16/0.64    ( ! [X24] : (~m1_subset_1(X24,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_2(k7_tmap_1(sK0,X24),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X24)))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f129,f54])).
% 2.16/0.64  fof(f129,plain,(
% 2.16/0.64    ( ! [X24] : (~m1_subset_1(X24,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_2(k7_tmap_1(sK0,X24),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,X24)))) )),
% 2.16/0.64    inference(superposition,[],[f83,f95])).
% 2.16/0.64  fof(f83,plain,(
% 2.16/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_2(k7_tmap_1(X0,X1),u1_struct_0(X0),u1_struct_0(k6_tmap_1(X0,X1)))) )),
% 2.16/0.64    inference(cnf_transformation,[],[f45])).
% 2.16/0.64  fof(f231,plain,(
% 2.16/0.64    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 2.16/0.64    inference(forward_demodulation,[],[f229,f224])).
% 2.16/0.64  fof(f229,plain,(
% 2.16/0.64    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 2.16/0.64    inference(backward_demodulation,[],[f214,f224])).
% 2.16/0.64  fof(f214,plain,(
% 2.16/0.64    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 2.16/0.64    inference(forward_demodulation,[],[f213,f204])).
% 2.16/0.64  fof(f213,plain,(
% 2.16/0.64    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v3_pre_topc(sK1,sK0)),
% 2.16/0.64    inference(forward_demodulation,[],[f212,f204])).
% 2.16/0.64  fof(f212,plain,(
% 2.16/0.64    ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v3_pre_topc(sK1,sK0)),
% 2.16/0.64    inference(backward_demodulation,[],[f202,f204])).
% 2.16/0.64  fof(f202,plain,(
% 2.16/0.64    ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 2.16/0.64    inference(subsumption_resolution,[],[f100,f201])).
% 2.16/0.64  fof(f201,plain,(
% 2.16/0.64    v1_funct_1(k7_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(resolution,[],[f164,f99])).
% 2.16/0.64  fof(f164,plain,(
% 2.16/0.64    ( ! [X23] : (~m1_subset_1(X23,k1_zfmisc_1(k2_struct_0(sK0))) | v1_funct_1(k7_tmap_1(sK0,X23))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f163,f53])).
% 2.16/0.64  fof(f163,plain,(
% 2.16/0.64    ( ! [X23] : (~m1_subset_1(X23,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | v1_funct_1(k7_tmap_1(sK0,X23))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f162,f55])).
% 2.16/0.64  fof(f162,plain,(
% 2.16/0.64    ( ! [X23] : (~m1_subset_1(X23,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_1(k7_tmap_1(sK0,X23))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f128,f54])).
% 2.16/0.64  fof(f128,plain,(
% 2.16/0.64    ( ! [X23] : (~m1_subset_1(X23,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v1_funct_1(k7_tmap_1(sK0,X23))) )),
% 2.16/0.64    inference(superposition,[],[f82,f95])).
% 2.16/0.64  fof(f82,plain,(
% 2.16/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v1_funct_1(k7_tmap_1(X0,X1))) )),
% 2.16/0.64    inference(cnf_transformation,[],[f45])).
% 2.16/0.64  fof(f100,plain,(
% 2.16/0.64    ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_2(k7_tmap_1(sK0,sK1),k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 2.16/0.64    inference(forward_demodulation,[],[f96,f95])).
% 2.16/0.64  fof(f96,plain,(
% 2.16/0.64    ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~v3_pre_topc(sK1,sK0)),
% 2.16/0.64    inference(backward_demodulation,[],[f47,f95])).
% 2.16/0.64  fof(f47,plain,(
% 2.16/0.64    ~v1_funct_1(k7_tmap_1(sK0,sK1)) | ~v1_funct_2(k7_tmap_1(sK0,sK1),u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))) | ~v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(k7_tmap_1(sK0,sK1),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(k6_tmap_1(sK0,sK1))))) | ~v3_pre_topc(sK1,sK0)),
% 2.16/0.64    inference(cnf_transformation,[],[f20])).
% 2.16/0.64  fof(f993,plain,(
% 2.16/0.64    v3_pre_topc(sK1,sK0) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(forward_demodulation,[],[f992,f516])).
% 2.16/0.64  fof(f516,plain,(
% 2.16/0.64    sK1 = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK1)),
% 2.16/0.64    inference(superposition,[],[f483,f104])).
% 2.16/0.64  fof(f104,plain,(
% 2.16/0.64    sK1 = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK1)),
% 2.16/0.64    inference(resolution,[],[f79,f99])).
% 2.16/0.64  fof(f79,plain,(
% 2.16/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1) )),
% 2.16/0.64    inference(cnf_transformation,[],[f41])).
% 2.16/0.64  fof(f41,plain,(
% 2.16/0.64    ! [X0,X1] : (k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1 | ~m1_subset_1(X1,k1_zfmisc_1(X0)))),
% 2.16/0.64    inference(ennf_transformation,[],[f2])).
% 2.16/0.64  fof(f2,axiom,(
% 2.16/0.64    ! [X0,X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => k8_relset_1(X0,X0,k6_partfun1(X0),X1) = X1)),
% 2.16/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_funct_2)).
% 2.16/0.64  fof(f483,plain,(
% 2.16/0.64    ( ! [X0] : (k10_relat_1(k6_partfun1(k2_struct_0(sK0)),X0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),X0)) )),
% 2.16/0.64    inference(resolution,[],[f246,f85])).
% 2.16/0.64  fof(f85,plain,(
% 2.16/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 2.16/0.64    inference(cnf_transformation,[],[f46])).
% 2.16/0.64  fof(f46,plain,(
% 2.16/0.64    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.16/0.64    inference(ennf_transformation,[],[f1])).
% 2.16/0.64  fof(f1,axiom,(
% 2.16/0.64    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 2.16/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 2.16/0.64  fof(f992,plain,(
% 2.16/0.64    v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK1),sK0) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(subsumption_resolution,[],[f990,f99])).
% 2.16/0.64  fof(f990,plain,(
% 2.16/0.64    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK1),sK0) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(resolution,[],[f627,f344])).
% 2.16/0.64  fof(f344,plain,(
% 2.16/0.64    v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(subsumption_resolution,[],[f343,f99])).
% 2.16/0.64  fof(f343,plain,(
% 2.16/0.64    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(forward_demodulation,[],[f342,f95])).
% 2.16/0.64  fof(f342,plain,(
% 2.16/0.64    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(subsumption_resolution,[],[f341,f53])).
% 2.16/0.64  fof(f341,plain,(
% 2.16/0.64    ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(subsumption_resolution,[],[f340,f55])).
% 2.16/0.64  fof(f340,plain,(
% 2.16/0.64    ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(subsumption_resolution,[],[f339,f54])).
% 2.16/0.64  fof(f339,plain,(
% 2.16/0.64    ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(subsumption_resolution,[],[f287,f99])).
% 2.16/0.64  fof(f287,plain,(
% 2.16/0.64    ~m1_subset_1(sK1,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~m1_subset_1(sK1,k1_zfmisc_1(u1_struct_0(sK0))) | v2_struct_0(sK0) | v3_pre_topc(sK1,k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(superposition,[],[f86,f224])).
% 2.16/0.64  fof(f86,plain,(
% 2.16/0.64    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X2)))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | v2_struct_0(X0) | v3_pre_topc(X2,k6_tmap_1(X0,X2))) )),
% 2.16/0.64    inference(equality_resolution,[],[f75])).
% 2.16/0.64  fof(f75,plain,(
% 2.16/0.64    ( ! [X2,X0,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) | X1 != X2 | v3_pre_topc(X2,k6_tmap_1(X0,X1))) )),
% 2.16/0.64    inference(cnf_transformation,[],[f36])).
% 2.16/0.64  fof(f36,plain,(
% 2.16/0.64    ! [X0] : (! [X1] : (! [X2] : (v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.16/0.64    inference(flattening,[],[f35])).
% 2.16/0.64  fof(f35,plain,(
% 2.16/0.64    ! [X0] : (! [X1] : (! [X2] : ((v3_pre_topc(X2,k6_tmap_1(X0,X1)) | X1 != X2) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1))))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.16/0.64    inference(ennf_transformation,[],[f14])).
% 2.16/0.64  fof(f14,axiom,(
% 2.16/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(k6_tmap_1(X0,X1)))) => (X1 = X2 => v3_pre_topc(X2,k6_tmap_1(X0,X1))))))),
% 2.16/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t105_tmap_1)).
% 2.16/0.64  fof(f627,plain,(
% 2.16/0.64    ( ! [X0] : (~v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),X0),sK0) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(forward_demodulation,[],[f626,f483])).
% 2.16/0.64  fof(f626,plain,(
% 2.16/0.64    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),X0),sK0) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f625,f239])).
% 2.16/0.64  fof(f625,plain,(
% 2.16/0.64    ( ! [X0] : (~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),X0),sK0) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f623,f211])).
% 2.16/0.64  fof(f211,plain,(
% 2.16/0.64    v1_funct_1(k6_partfun1(k2_struct_0(sK0)))),
% 2.16/0.64    inference(backward_demodulation,[],[f201,f204])).
% 2.16/0.64  fof(f623,plain,(
% 2.16/0.64    ( ! [X0] : (~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X0,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),X0),sK0) | ~v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(resolution,[],[f433,f246])).
% 2.16/0.64  fof(f433,plain,(
% 2.16/0.64    ( ! [X70,X71] : (~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_1(X70) | ~v1_funct_2(X70,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X71,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X71,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X70,X71),sK0) | ~v5_pre_topc(X70,sK0,k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f432,f430])).
% 2.16/0.64  fof(f430,plain,(
% 2.16/0.64    ( ! [X66,X67] : (~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_1(X66) | ~v1_funct_2(X66,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X67,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X67,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X66,X67),sK0) | ~v5_pre_topc(X66,sK0,k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(forward_demodulation,[],[f429,f259])).
% 2.16/0.64  fof(f259,plain,(
% 2.16/0.64    k2_struct_0(sK0) = k2_struct_0(k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(forward_demodulation,[],[f258,f224])).
% 2.16/0.64  fof(f258,plain,(
% 2.16/0.64    u1_struct_0(k6_tmap_1(sK0,sK1)) = k2_struct_0(k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(resolution,[],[f232,f56])).
% 2.16/0.64  fof(f232,plain,(
% 2.16/0.64    l1_struct_0(k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(resolution,[],[f200,f57])).
% 2.16/0.64  fof(f200,plain,(
% 2.16/0.64    l1_pre_topc(k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(resolution,[],[f161,f99])).
% 2.16/0.64  fof(f161,plain,(
% 2.16/0.64    ( ! [X22] : (~m1_subset_1(X22,k1_zfmisc_1(k2_struct_0(sK0))) | l1_pre_topc(k6_tmap_1(sK0,X22))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f160,f53])).
% 2.16/0.64  fof(f160,plain,(
% 2.16/0.64    ( ! [X22] : (~m1_subset_1(X22,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | l1_pre_topc(k6_tmap_1(sK0,X22))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f159,f55])).
% 2.16/0.64  fof(f159,plain,(
% 2.16/0.64    ( ! [X22] : (~m1_subset_1(X22,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | l1_pre_topc(k6_tmap_1(sK0,X22))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f127,f54])).
% 2.16/0.64  fof(f127,plain,(
% 2.16/0.64    ( ! [X22] : (~m1_subset_1(X22,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | l1_pre_topc(k6_tmap_1(sK0,X22))) )),
% 2.16/0.64    inference(superposition,[],[f81,f95])).
% 2.16/0.64  fof(f81,plain,(
% 2.16/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | l1_pre_topc(k6_tmap_1(X0,X1))) )),
% 2.16/0.64    inference(cnf_transformation,[],[f43])).
% 2.16/0.64  fof(f43,plain,(
% 2.16/0.64    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.16/0.64    inference(flattening,[],[f42])).
% 2.16/0.64  fof(f42,plain,(
% 2.16/0.64    ! [X0,X1] : ((l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.16/0.64    inference(ennf_transformation,[],[f18])).
% 2.16/0.64  fof(f18,plain,(
% 2.16/0.64    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1))))),
% 2.16/0.64    inference(pure_predicate_removal,[],[f10])).
% 2.16/0.64  fof(f10,axiom,(
% 2.16/0.64    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => (l1_pre_topc(k6_tmap_1(X0,X1)) & v2_pre_topc(k6_tmap_1(X0,X1)) & v1_pre_topc(k6_tmap_1(X0,X1))))),
% 2.16/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_tmap_1)).
% 2.16/0.64  fof(f429,plain,(
% 2.16/0.64    ( ! [X66,X67] : (~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_1(X66) | ~v1_funct_2(X66,k2_struct_0(sK0),k2_struct_0(sK0)) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X67,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X67,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X66,X67),sK0) | ~v5_pre_topc(X66,sK0,k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f331,f200])).
% 2.16/0.64  fof(f331,plain,(
% 2.16/0.64    ( ! [X66,X67] : (~m1_subset_1(X66,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X66) | ~v1_funct_2(X66,k2_struct_0(sK0),k2_struct_0(sK0)) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~m1_subset_1(X67,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X67,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X66,X67),sK0) | ~v5_pre_topc(X66,sK0,k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(superposition,[],[f181,f224])).
% 2.16/0.64  fof(f181,plain,(
% 2.16/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1)))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1)) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X2,X1) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X1),X0,X2),sK0) | ~v5_pre_topc(X0,sK0,X1)) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f179,f55])).
% 2.16/0.64  fof(f179,plain,(
% 2.16/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1)))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1)) | ~l1_pre_topc(sK0) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X2,X1) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X1),X0,X2),sK0) | ~v5_pre_topc(X0,sK0,X1)) )),
% 2.16/0.64    inference(superposition,[],[f58,f95])).
% 2.16/0.64  fof(f58,plain,(
% 2.16/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0) | k2_struct_0(X1) = k1_xboole_0 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1) | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v5_pre_topc(X2,X0,X1)) )),
% 2.16/0.64    inference(cnf_transformation,[],[f24])).
% 2.16/0.64  fof(f24,plain,(
% 2.16/0.64    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.16/0.64    inference(flattening,[],[f23])).
% 2.16/0.64  fof(f23,plain,(
% 2.16/0.64    ! [X0] : (! [X1] : (! [X2] : (((v5_pre_topc(X2,X0,X1) <=> ! [X3] : ((v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v3_pre_topc(X3,X1)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))))) | (k2_struct_0(X0) != k1_xboole_0 & k2_struct_0(X1) = k1_xboole_0)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 2.16/0.64    inference(ennf_transformation,[],[f8])).
% 2.16/0.64  fof(f8,axiom,(
% 2.16/0.64    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k2_struct_0(X1) = k1_xboole_0 => k2_struct_0(X0) = k1_xboole_0) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => (v3_pre_topc(X3,X1) => v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0))))))))),
% 2.16/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_tops_2)).
% 2.16/0.64  fof(f432,plain,(
% 2.16/0.64    ( ! [X70,X71] : (~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_1(X70) | ~v1_funct_2(X70,k2_struct_0(sK0),k2_struct_0(sK0)) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X71,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X71,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X70,X71),sK0) | ~v5_pre_topc(X70,sK0,k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f333,f200])).
% 2.16/0.64  fof(f333,plain,(
% 2.16/0.64    ( ! [X70,X71] : (~m1_subset_1(X70,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X70) | ~v1_funct_2(X70,k2_struct_0(sK0),k2_struct_0(sK0)) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X71,k1_zfmisc_1(k2_struct_0(sK0))) | ~v3_pre_topc(X71,k6_tmap_1(sK0,sK1)) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X70,X71),sK0) | ~v5_pre_topc(X70,sK0,k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(superposition,[],[f185,f224])).
% 2.16/0.64  fof(f185,plain,(
% 2.16/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1)))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1)) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X2,X1) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X1),X0,X2),sK0) | ~v5_pre_topc(X0,sK0,X1)) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f183,f55])).
% 2.16/0.64  fof(f183,plain,(
% 2.16/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1)))) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1)) | ~l1_pre_topc(sK0) | k1_xboole_0 != k2_struct_0(sK0) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X2,X1) | v3_pre_topc(k8_relset_1(k2_struct_0(sK0),u1_struct_0(X1),X0,X2),sK0) | ~v5_pre_topc(X0,sK0,X1)) )),
% 2.16/0.64    inference(superposition,[],[f62,f95])).
% 2.16/0.64  fof(f62,plain,(
% 2.16/0.64    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0) | k2_struct_0(X0) != k1_xboole_0 | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | ~v3_pre_topc(X3,X1) | v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3),X0) | ~v5_pre_topc(X2,X0,X1)) )),
% 2.16/0.64    inference(cnf_transformation,[],[f24])).
% 2.16/0.64  fof(f2437,plain,(
% 2.16/0.64    v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(subsumption_resolution,[],[f2436,f211])).
% 2.16/0.64  fof(f2436,plain,(
% 2.16/0.64    ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(subsumption_resolution,[],[f2435,f246])).
% 2.16/0.64  fof(f2435,plain,(
% 2.16/0.64    ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(subsumption_resolution,[],[f2422,f239])).
% 2.16/0.64  fof(f2422,plain,(
% 2.16/0.64    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(resolution,[],[f2418,f1073])).
% 2.16/0.64  fof(f1073,plain,(
% 2.16/0.64    ( ! [X74] : (~v5_pre_topc(X74,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | ~v1_funct_2(X74,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_1(X74) | v5_pre_topc(X74,sK0,k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(forward_demodulation,[],[f1072,f1029])).
% 2.16/0.64  fof(f1029,plain,(
% 2.16/0.64    k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),
% 2.16/0.64    inference(subsumption_resolution,[],[f243,f995])).
% 2.16/0.64  fof(f995,plain,(
% 2.16/0.64    v3_pre_topc(sK1,sK0)),
% 2.16/0.64    inference(subsumption_resolution,[],[f206,f994])).
% 2.16/0.64  fof(f206,plain,(
% 2.16/0.64    v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)),
% 2.16/0.64    inference(backward_demodulation,[],[f50,f204])).
% 2.16/0.64  fof(f50,plain,(
% 2.16/0.64    v5_pre_topc(k7_tmap_1(sK0,sK1),sK0,k6_tmap_1(sK0,sK1)) | v3_pre_topc(sK1,sK0)),
% 2.16/0.64    inference(cnf_transformation,[],[f20])).
% 2.16/0.64  fof(f243,plain,(
% 2.16/0.64    ~v3_pre_topc(sK1,sK0) | k6_tmap_1(sK0,sK1) = g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),
% 2.16/0.64    inference(resolution,[],[f155,f99])).
% 2.16/0.64  fof(f155,plain,(
% 2.16/0.64    ( ! [X20] : (~m1_subset_1(X20,k1_zfmisc_1(k2_struct_0(sK0))) | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X20) | ~v3_pre_topc(X20,sK0)) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f154,f53])).
% 2.16/0.64  fof(f154,plain,(
% 2.16/0.64    ( ! [X20] : (~m1_subset_1(X20,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X20) | ~v3_pre_topc(X20,sK0)) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f153,f55])).
% 2.16/0.64  fof(f153,plain,(
% 2.16/0.64    ( ! [X20] : (~m1_subset_1(X20,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X20) | ~v3_pre_topc(X20,sK0)) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f125,f54])).
% 2.16/0.64  fof(f125,plain,(
% 2.16/0.64    ( ! [X20] : (~m1_subset_1(X20,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)) = k6_tmap_1(sK0,X20) | ~v3_pre_topc(X20,sK0)) )),
% 2.16/0.64    inference(superposition,[],[f74,f95])).
% 2.16/0.64  fof(f74,plain,(
% 2.16/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1) | ~v3_pre_topc(X1,X0)) )),
% 2.16/0.64    inference(cnf_transformation,[],[f34])).
% 2.16/0.64  fof(f34,plain,(
% 2.16/0.64    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 2.16/0.64    inference(flattening,[],[f33])).
% 2.16/0.64  fof(f33,plain,(
% 2.16/0.64    ! [X0] : (! [X1] : ((v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 2.16/0.64    inference(ennf_transformation,[],[f15])).
% 2.16/0.64  fof(f15,axiom,(
% 2.16/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) => (v3_pre_topc(X1,X0) <=> g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)) = k6_tmap_1(X0,X1))))),
% 2.16/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_tmap_1)).
% 2.16/0.64  fof(f1072,plain,(
% 2.16/0.64    ( ! [X74] : (~v1_funct_2(X74,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_1(X74) | ~v5_pre_topc(X74,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | v5_pre_topc(X74,sK0,k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(duplicate_literal_removal,[],[f1071])).
% 2.16/0.64  fof(f1071,plain,(
% 2.16/0.64    ( ! [X74] : (~v1_funct_2(X74,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_1(X74) | ~v1_funct_2(X74,k2_struct_0(sK0),k2_struct_0(sK0)) | ~v5_pre_topc(X74,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | v5_pre_topc(X74,sK0,k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(forward_demodulation,[],[f1070,f224])).
% 2.16/0.64  fof(f1070,plain,(
% 2.16/0.64    ( ! [X74] : (~v1_funct_2(X74,u1_struct_0(k6_tmap_1(sK0,sK1)),k2_struct_0(sK0)) | ~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_1(X74) | ~v1_funct_2(X74,k2_struct_0(sK0),k2_struct_0(sK0)) | ~v5_pre_topc(X74,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | v5_pre_topc(X74,sK0,k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(forward_demodulation,[],[f1069,f1029])).
% 2.16/0.64  fof(f1069,plain,(
% 2.16/0.64    ( ! [X74] : (~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_1(X74) | ~v1_funct_2(X74,k2_struct_0(sK0),k2_struct_0(sK0)) | ~v1_funct_2(X74,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(sK0)) | ~v5_pre_topc(X74,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | v5_pre_topc(X74,sK0,k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(duplicate_literal_removal,[],[f1068])).
% 2.16/0.64  fof(f1068,plain,(
% 2.16/0.64    ( ! [X74] : (~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_1(X74) | ~v1_funct_2(X74,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(X74,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(sK0)) | ~v5_pre_topc(X74,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | v5_pre_topc(X74,sK0,k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(forward_demodulation,[],[f1037,f224])).
% 2.16/0.64  fof(f1037,plain,(
% 2.16/0.64    ( ! [X74] : (~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(k6_tmap_1(sK0,sK1)),k2_struct_0(sK0)))) | ~v1_funct_1(X74) | ~v1_funct_2(X74,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(X74,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(sK0)) | ~v5_pre_topc(X74,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | v5_pre_topc(X74,sK0,k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(backward_demodulation,[],[f438,f1029])).
% 2.16/0.64  fof(f438,plain,(
% 2.16/0.64    ( ! [X74] : (~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(sK0)))) | ~v1_funct_1(X74) | ~v1_funct_2(X74,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(X74,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(sK0)) | ~v5_pre_topc(X74,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | v5_pre_topc(X74,sK0,k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f437,f200])).
% 2.16/0.64  fof(f437,plain,(
% 2.16/0.64    ( ! [X74] : (~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(sK0)))) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X74) | ~v1_funct_2(X74,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(X74,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(sK0)) | ~v5_pre_topc(X74,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | v5_pre_topc(X74,sK0,k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f335,f199])).
% 2.16/0.64  fof(f199,plain,(
% 2.16/0.64    v2_pre_topc(k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(resolution,[],[f158,f99])).
% 2.16/0.64  fof(f158,plain,(
% 2.16/0.64    ( ! [X21] : (~m1_subset_1(X21,k1_zfmisc_1(k2_struct_0(sK0))) | v2_pre_topc(k6_tmap_1(sK0,X21))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f157,f53])).
% 2.16/0.64  fof(f157,plain,(
% 2.16/0.64    ( ! [X21] : (~m1_subset_1(X21,k1_zfmisc_1(k2_struct_0(sK0))) | v2_struct_0(sK0) | v2_pre_topc(k6_tmap_1(sK0,X21))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f156,f55])).
% 2.16/0.64  fof(f156,plain,(
% 2.16/0.64    ( ! [X21] : (~m1_subset_1(X21,k1_zfmisc_1(k2_struct_0(sK0))) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_pre_topc(k6_tmap_1(sK0,X21))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f126,f54])).
% 2.16/0.64  fof(f126,plain,(
% 2.16/0.64    ( ! [X21] : (~m1_subset_1(X21,k1_zfmisc_1(k2_struct_0(sK0))) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | v2_struct_0(sK0) | v2_pre_topc(k6_tmap_1(sK0,X21))) )),
% 2.16/0.64    inference(superposition,[],[f80,f95])).
% 2.16/0.64  fof(f80,plain,(
% 2.16/0.64    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | v2_struct_0(X0) | v2_pre_topc(k6_tmap_1(X0,X1))) )),
% 2.16/0.64    inference(cnf_transformation,[],[f43])).
% 2.16/0.64  fof(f335,plain,(
% 2.16/0.64    ( ! [X74] : (~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(sK0)))) | ~v2_pre_topc(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X74) | ~v1_funct_2(X74,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X74,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_2(X74,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),k2_struct_0(sK0)) | ~v5_pre_topc(X74,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),k6_tmap_1(sK0,sK1)) | v5_pre_topc(X74,sK0,k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(superposition,[],[f190,f224])).
% 2.16/0.64  fof(f190,plain,(
% 2.16/0.64    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~v5_pre_topc(X0,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X1) | v5_pre_topc(X0,sK0,X1)) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f189,f54])).
% 2.16/0.64  fof(f189,plain,(
% 2.16/0.64    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)))) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~v2_pre_topc(sK0) | ~v5_pre_topc(X0,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X1) | v5_pre_topc(X0,sK0,X1)) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f187,f55])).
% 2.16/0.64  fof(f187,plain,(
% 2.16/0.64    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)))) | ~l1_pre_topc(sK0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k2_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(X0,u1_struct_0(g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0))),u1_struct_0(X1)) | ~v2_pre_topc(sK0) | ~v5_pre_topc(X0,g1_pre_topc(k2_struct_0(sK0),u1_pre_topc(sK0)),X1) | v5_pre_topc(X0,sK0,X1)) )),
% 2.16/0.64    inference(superposition,[],[f89,f95])).
% 2.16/0.64  fof(f89,plain,(
% 2.16/0.64    ( ! [X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v2_pre_topc(X0) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1)) )),
% 2.16/0.64    inference(duplicate_literal_removal,[],[f88])).
% 2.16/0.64  fof(f88,plain,(
% 2.16/0.64    ( ! [X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X3,X0,X1)) )),
% 2.16/0.64    inference(equality_resolution,[],[f76])).
% 2.16/0.64  fof(f76,plain,(
% 2.16/0.64    ( ! [X2,X0,X3,X1] : (~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | X2 != X3 | ~v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1) | v5_pre_topc(X2,X0,X1)) )),
% 2.16/0.64    inference(cnf_transformation,[],[f38])).
% 2.16/0.64  fof(f38,plain,(
% 2.16/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 2.16/0.64    inference(flattening,[],[f37])).
% 2.16/0.64  fof(f37,plain,(
% 2.16/0.64    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (((v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)) | X2 != X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) | ~v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 2.16/0.64    inference(ennf_transformation,[],[f7])).
% 2.16/0.64  fof(f7,axiom,(
% 2.16/0.64    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)))) & v1_funct_2(X3,u1_struct_0(g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0))),u1_struct_0(X1)) & v1_funct_1(X3)) => (X2 = X3 => (v5_pre_topc(X2,X0,X1) <=> v5_pre_topc(X3,g1_pre_topc(u1_struct_0(X0),u1_pre_topc(X0)),X1)))))))),
% 2.16/0.64    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_pre_topc)).
% 2.16/0.64  fof(f2418,plain,(
% 2.16/0.64    v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(subsumption_resolution,[],[f2417,f1304])).
% 2.16/0.64  fof(f1304,plain,(
% 2.16/0.64    v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(subsumption_resolution,[],[f1303,f239])).
% 2.16/0.64  fof(f1303,plain,(
% 2.16/0.64    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(subsumption_resolution,[],[f1301,f211])).
% 2.16/0.64  fof(f1301,plain,(
% 2.16/0.64    ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(resolution,[],[f590,f246])).
% 2.16/0.64  fof(f590,plain,(
% 2.16/0.64    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1),k6_tmap_1(sK0,sK1)) | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f589,f586])).
% 2.16/0.64  fof(f586,plain,(
% 2.16/0.64    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1),k6_tmap_1(sK0,sK1)) | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(forward_demodulation,[],[f585,f259])).
% 2.16/0.64  fof(f585,plain,(
% 2.16/0.64    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1),k6_tmap_1(sK0,sK1)) | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f584,f200])).
% 2.16/0.64  fof(f584,plain,(
% 2.16/0.64    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1),k6_tmap_1(sK0,sK1)) | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(superposition,[],[f351,f224])).
% 2.16/0.64  fof(f351,plain,(
% 2.16/0.64    ( ! [X10,X11] : (~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X11)))) | ~l1_pre_topc(X11) | ~v1_funct_1(X10) | ~v1_funct_2(X10,k2_struct_0(sK0),u1_struct_0(X11)) | k1_xboole_0 = k2_struct_0(X11) | v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),X11,X10),X11) | v5_pre_topc(X10,k6_tmap_1(sK0,sK1),X11)) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f292,f200])).
% 2.16/0.64  fof(f292,plain,(
% 2.16/0.64    ( ! [X10,X11] : (~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X11)))) | ~l1_pre_topc(X11) | ~v1_funct_1(X10) | ~v1_funct_2(X10,k2_struct_0(sK0),u1_struct_0(X11)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(X11) | v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),X11,X10),X11) | v5_pre_topc(X10,k6_tmap_1(sK0,sK1),X11)) )),
% 2.16/0.64    inference(superposition,[],[f60,f224])).
% 2.16/0.64  fof(f60,plain,(
% 2.16/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0) | k2_struct_0(X1) = k1_xboole_0 | v3_pre_topc(sK2(X0,X1,X2),X1) | v5_pre_topc(X2,X0,X1)) )),
% 2.16/0.64    inference(cnf_transformation,[],[f24])).
% 2.16/0.64  fof(f589,plain,(
% 2.16/0.64    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | k1_xboole_0 != k2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1),k6_tmap_1(sK0,sK1)) | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f588,f200])).
% 2.16/0.64  fof(f588,plain,(
% 2.16/0.64    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | k1_xboole_0 != k2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1),k6_tmap_1(sK0,sK1)) | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(superposition,[],[f364,f224])).
% 2.16/0.64  fof(f364,plain,(
% 2.16/0.64    ( ! [X28,X29] : (~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X29)))) | k1_xboole_0 != k2_struct_0(sK0) | ~l1_pre_topc(X29) | ~v1_funct_1(X28) | ~v1_funct_2(X28,k2_struct_0(sK0),u1_struct_0(X29)) | v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),X29,X28),X29) | v5_pre_topc(X28,k6_tmap_1(sK0,sK1),X29)) )),
% 2.16/0.64    inference(forward_demodulation,[],[f363,f259])).
% 2.16/0.64  fof(f363,plain,(
% 2.16/0.64    ( ! [X28,X29] : (~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X29)))) | ~l1_pre_topc(X29) | ~v1_funct_1(X28) | ~v1_funct_2(X28,k2_struct_0(sK0),u1_struct_0(X29)) | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1)) | v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),X29,X28),X29) | v5_pre_topc(X28,k6_tmap_1(sK0,sK1),X29)) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f300,f200])).
% 2.16/0.64  fof(f300,plain,(
% 2.16/0.64    ( ! [X28,X29] : (~m1_subset_1(X28,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X29)))) | ~l1_pre_topc(X29) | ~v1_funct_1(X28) | ~v1_funct_2(X28,k2_struct_0(sK0),u1_struct_0(X29)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1)) | v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),X29,X28),X29) | v5_pre_topc(X28,k6_tmap_1(sK0,sK1),X29)) )),
% 2.16/0.64    inference(superposition,[],[f64,f224])).
% 2.16/0.64  fof(f64,plain,(
% 2.16/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0) | k2_struct_0(X0) != k1_xboole_0 | v3_pre_topc(sK2(X0,X1,X2),X1) | v5_pre_topc(X2,X0,X1)) )),
% 2.16/0.64    inference(cnf_transformation,[],[f24])).
% 2.16/0.64  fof(f2417,plain,(
% 2.16/0.64    ~v3_pre_topc(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k6_tmap_1(sK0,sK1)) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(backward_demodulation,[],[f1316,f2415])).
% 2.16/0.64  fof(f2415,plain,(
% 2.16/0.64    sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))))),
% 2.16/0.64    inference(subsumption_resolution,[],[f2414,f994])).
% 2.16/0.64  fof(f2414,plain,(
% 2.16/0.64    sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(subsumption_resolution,[],[f2413,f211])).
% 2.16/0.64  fof(f2413,plain,(
% 2.16/0.64    sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(subsumption_resolution,[],[f2412,f246])).
% 2.16/0.64  fof(f2412,plain,(
% 2.16/0.64    sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(subsumption_resolution,[],[f2399,f239])).
% 2.16/0.64  fof(f2399,plain,(
% 2.16/0.64    sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),sK0,k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(resolution,[],[f1737,f1073])).
% 2.16/0.64  fof(f1737,plain,(
% 2.16/0.64    v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))))),
% 2.16/0.64    inference(forward_demodulation,[],[f1735,f483])).
% 2.16/0.64  fof(f1735,plain,(
% 2.16/0.64    v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1)) | sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),k6_partfun1(k2_struct_0(sK0)),sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))))),
% 2.16/0.64    inference(resolution,[],[f1308,f79])).
% 2.16/0.64  fof(f1308,plain,(
% 2.16/0.64    m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(subsumption_resolution,[],[f1307,f239])).
% 2.16/0.64  fof(f1307,plain,(
% 2.16/0.64    ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(subsumption_resolution,[],[f1305,f211])).
% 2.16/0.64  fof(f1305,plain,(
% 2.16/0.64    ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0))),k1_zfmisc_1(k2_struct_0(sK0))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))),
% 2.16/0.64    inference(resolution,[],[f613,f246])).
% 2.16/0.64  fof(f613,plain,(
% 2.16/0.64    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1),k1_zfmisc_1(k2_struct_0(sK0))) | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f612,f605])).
% 2.16/0.64  fof(f605,plain,(
% 2.16/0.64    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1),k1_zfmisc_1(k2_struct_0(sK0))) | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(forward_demodulation,[],[f604,f259])).
% 2.16/0.64  fof(f604,plain,(
% 2.16/0.64    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1),k1_zfmisc_1(k2_struct_0(sK0))) | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f603,f200])).
% 2.16/0.64  fof(f603,plain,(
% 2.16/0.64    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1),k1_zfmisc_1(k2_struct_0(sK0))) | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 2.16/0.64    inference(superposition,[],[f348,f224])).
% 2.16/0.64  fof(f348,plain,(
% 2.16/0.64    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X7)))) | ~l1_pre_topc(X7) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k2_struct_0(sK0),u1_struct_0(X7)) | k1_xboole_0 = k2_struct_0(X7) | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),X7,X6),k1_zfmisc_1(u1_struct_0(X7))) | v5_pre_topc(X6,k6_tmap_1(sK0,sK1),X7)) )),
% 2.16/0.64    inference(subsumption_resolution,[],[f290,f200])).
% 2.16/0.64  fof(f290,plain,(
% 2.16/0.64    ( ! [X6,X7] : (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X7)))) | ~l1_pre_topc(X7) | ~v1_funct_1(X6) | ~v1_funct_2(X6,k2_struct_0(sK0),u1_struct_0(X7)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(X7) | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),X7,X6),k1_zfmisc_1(u1_struct_0(X7))) | v5_pre_topc(X6,k6_tmap_1(sK0,sK1),X7)) )),
% 2.16/0.64    inference(superposition,[],[f59,f224])).
% 2.16/0.64  fof(f59,plain,(
% 2.16/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0) | k2_struct_0(X1) = k1_xboole_0 | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | v5_pre_topc(X2,X0,X1)) )),
% 2.16/0.64    inference(cnf_transformation,[],[f24])).
% 2.32/0.64  fof(f612,plain,(
% 2.32/0.64    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | k1_xboole_0 != k2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1),k1_zfmisc_1(k2_struct_0(sK0))) | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 2.32/0.64    inference(subsumption_resolution,[],[f611,f200])).
% 2.32/0.64  fof(f611,plain,(
% 2.32/0.64    ( ! [X1] : (~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | k1_xboole_0 != k2_struct_0(sK0) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1),k1_zfmisc_1(k2_struct_0(sK0))) | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 2.32/0.64    inference(superposition,[],[f361,f224])).
% 2.32/0.64  fof(f361,plain,(
% 2.32/0.64    ( ! [X24,X25] : (~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X25)))) | k1_xboole_0 != k2_struct_0(sK0) | ~l1_pre_topc(X25) | ~v1_funct_1(X24) | ~v1_funct_2(X24,k2_struct_0(sK0),u1_struct_0(X25)) | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),X25,X24),k1_zfmisc_1(u1_struct_0(X25))) | v5_pre_topc(X24,k6_tmap_1(sK0,sK1),X25)) )),
% 2.32/0.64    inference(forward_demodulation,[],[f360,f259])).
% 2.32/0.64  fof(f360,plain,(
% 2.32/0.64    ( ! [X24,X25] : (~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X25)))) | ~l1_pre_topc(X25) | ~v1_funct_1(X24) | ~v1_funct_2(X24,k2_struct_0(sK0),u1_struct_0(X25)) | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1)) | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),X25,X24),k1_zfmisc_1(u1_struct_0(X25))) | v5_pre_topc(X24,k6_tmap_1(sK0,sK1),X25)) )),
% 2.32/0.64    inference(subsumption_resolution,[],[f298,f200])).
% 2.32/0.64  fof(f298,plain,(
% 2.32/0.64    ( ! [X24,X25] : (~m1_subset_1(X24,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X25)))) | ~l1_pre_topc(X25) | ~v1_funct_1(X24) | ~v1_funct_2(X24,k2_struct_0(sK0),u1_struct_0(X25)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1)) | m1_subset_1(sK2(k6_tmap_1(sK0,sK1),X25,X24),k1_zfmisc_1(u1_struct_0(X25))) | v5_pre_topc(X24,k6_tmap_1(sK0,sK1),X25)) )),
% 2.32/0.64    inference(superposition,[],[f63,f224])).
% 2.32/0.64  fof(f63,plain,(
% 2.32/0.64    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_pre_topc(X0) | k2_struct_0(X0) != k1_xboole_0 | m1_subset_1(sK2(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | v5_pre_topc(X2,X0,X1)) )),
% 2.32/0.64    inference(cnf_transformation,[],[f24])).
% 2.32/0.64  fof(f1316,plain,(
% 2.32/0.64    ~v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),k6_tmap_1(sK0,sK1)) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))),
% 2.32/0.64    inference(subsumption_resolution,[],[f1315,f246])).
% 2.32/0.64  fof(f1315,plain,(
% 2.32/0.64    ~v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),k6_tmap_1(sK0,sK1)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))),
% 2.32/0.64    inference(subsumption_resolution,[],[f1314,f239])).
% 2.32/0.64  fof(f1314,plain,(
% 2.32/0.64    ~v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),k6_tmap_1(sK0,sK1)) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))),
% 2.32/0.64    inference(subsumption_resolution,[],[f1313,f211])).
% 2.32/0.64  fof(f1313,plain,(
% 2.32/0.64    ~v3_pre_topc(k10_relat_1(k6_partfun1(k2_struct_0(sK0)),sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),k6_partfun1(k2_struct_0(sK0)))),k6_tmap_1(sK0,sK1)) | ~v1_funct_1(k6_partfun1(k2_struct_0(sK0))) | ~v1_funct_2(k6_partfun1(k2_struct_0(sK0)),k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(k6_partfun1(k2_struct_0(sK0)),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | v5_pre_topc(k6_partfun1(k2_struct_0(sK0)),k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))),
% 2.32/0.64    inference(superposition,[],[f647,f483])).
% 2.32/0.64  fof(f647,plain,(
% 2.32/0.64    ( ! [X1] : (~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1)),k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 2.32/0.64    inference(subsumption_resolution,[],[f646,f642])).
% 2.32/0.64  fof(f642,plain,(
% 2.32/0.64    ( ! [X1] : (~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1)),k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 2.32/0.64    inference(subsumption_resolution,[],[f641,f200])).
% 2.32/0.64  fof(f641,plain,(
% 2.32/0.64    ( ! [X1] : (~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1)),k6_tmap_1(sK0,sK1)) | k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 2.32/0.64    inference(superposition,[],[f356,f224])).
% 2.32/0.64  fof(f356,plain,(
% 2.32/0.64    ( ! [X17,X16] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X16),k2_struct_0(sK0),X17,sK2(X16,k6_tmap_1(sK0,sK1),X17)),X16) | k1_xboole_0 = k2_struct_0(sK0) | ~v1_funct_1(X17) | ~v1_funct_2(X17,u1_struct_0(X16),k2_struct_0(sK0)) | ~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),k2_struct_0(sK0)))) | ~l1_pre_topc(X16) | v5_pre_topc(X17,X16,k6_tmap_1(sK0,sK1))) )),
% 2.32/0.64    inference(forward_demodulation,[],[f355,f259])).
% 2.32/0.64  fof(f355,plain,(
% 2.32/0.64    ( ! [X17,X16] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X16),k2_struct_0(sK0),X17,sK2(X16,k6_tmap_1(sK0,sK1),X17)),X16) | ~v1_funct_1(X17) | ~v1_funct_2(X17,u1_struct_0(X16),k2_struct_0(sK0)) | ~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),k2_struct_0(sK0)))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(X16) | v5_pre_topc(X17,X16,k6_tmap_1(sK0,sK1))) )),
% 2.32/0.64    inference(subsumption_resolution,[],[f295,f200])).
% 2.32/0.64  fof(f295,plain,(
% 2.32/0.64    ( ! [X17,X16] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X16),k2_struct_0(sK0),X17,sK2(X16,k6_tmap_1(sK0,sK1),X17)),X16) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X17) | ~v1_funct_2(X17,u1_struct_0(X16),k2_struct_0(sK0)) | ~m1_subset_1(X17,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X16),k2_struct_0(sK0)))) | k1_xboole_0 = k2_struct_0(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(X16) | v5_pre_topc(X17,X16,k6_tmap_1(sK0,sK1))) )),
% 2.32/0.64    inference(superposition,[],[f61,f224])).
% 2.32/0.64  fof(f61,plain,(
% 2.32/0.64    ( ! [X2,X0,X1] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X1) = k1_xboole_0 | ~l1_pre_topc(X0) | v5_pre_topc(X2,X0,X1)) )),
% 2.32/0.64    inference(cnf_transformation,[],[f24])).
% 2.32/0.64  fof(f646,plain,(
% 2.32/0.64    ( ! [X1] : (k1_xboole_0 != k2_struct_0(sK0) | ~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1)),k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 2.32/0.64    inference(forward_demodulation,[],[f645,f259])).
% 2.32/0.64  fof(f645,plain,(
% 2.32/0.64    ( ! [X1] : (~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1)),k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1)) | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 2.32/0.64    inference(subsumption_resolution,[],[f644,f200])).
% 2.32/0.64  fof(f644,plain,(
% 2.32/0.64    ( ! [X1] : (~v3_pre_topc(k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK0),X1,sK2(k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1),X1)),k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,k2_struct_0(sK0),k2_struct_0(sK0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK0)))) | k1_xboole_0 != k2_struct_0(k6_tmap_1(sK0,sK1)) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | v5_pre_topc(X1,k6_tmap_1(sK0,sK1),k6_tmap_1(sK0,sK1))) )),
% 2.32/0.64    inference(superposition,[],[f368,f224])).
% 2.32/0.64  fof(f368,plain,(
% 2.32/0.64    ( ! [X35,X34] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X34),k2_struct_0(sK0),X35,sK2(X34,k6_tmap_1(sK0,sK1),X35)),X34) | ~v1_funct_1(X35) | ~v1_funct_2(X35,u1_struct_0(X34),k2_struct_0(sK0)) | ~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),k2_struct_0(sK0)))) | k1_xboole_0 != k2_struct_0(X34) | ~l1_pre_topc(X34) | v5_pre_topc(X35,X34,k6_tmap_1(sK0,sK1))) )),
% 2.32/0.64    inference(subsumption_resolution,[],[f303,f200])).
% 2.32/0.64  fof(f303,plain,(
% 2.32/0.64    ( ! [X35,X34] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X34),k2_struct_0(sK0),X35,sK2(X34,k6_tmap_1(sK0,sK1),X35)),X34) | ~l1_pre_topc(k6_tmap_1(sK0,sK1)) | ~v1_funct_1(X35) | ~v1_funct_2(X35,u1_struct_0(X34),k2_struct_0(sK0)) | ~m1_subset_1(X35,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X34),k2_struct_0(sK0)))) | k1_xboole_0 != k2_struct_0(X34) | ~l1_pre_topc(X34) | v5_pre_topc(X35,X34,k6_tmap_1(sK0,sK1))) )),
% 2.32/0.64    inference(superposition,[],[f65,f224])).
% 2.32/0.64  fof(f65,plain,(
% 2.32/0.64    ( ! [X2,X0,X1] : (~v3_pre_topc(k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK2(X0,X1,X2)),X0) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X0) != k1_xboole_0 | ~l1_pre_topc(X0) | v5_pre_topc(X2,X0,X1)) )),
% 2.32/0.64    inference(cnf_transformation,[],[f24])).
% 2.32/0.64  % SZS output end Proof for theBenchmark
% 2.32/0.64  % (32724)------------------------------
% 2.32/0.64  % (32724)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.32/0.64  % (32724)Termination reason: Refutation
% 2.32/0.64  
% 2.32/0.64  % (32724)Memory used [KB]: 3582
% 2.32/0.64  % (32724)Time elapsed: 0.219 s
% 2.32/0.64  % (32724)------------------------------
% 2.32/0.64  % (32724)------------------------------
% 2.32/0.65  % (32705)Success in time 0.287 s
%------------------------------------------------------------------------------
