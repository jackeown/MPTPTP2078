%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:01:58 EST 2020

% Result     : Theorem 1.84s
% Output     : Refutation 1.84s
% Verified   : 
% Statistics : Number of formulae       :   98 (2649 expanded)
%              Number of leaves         :   10 ( 500 expanded)
%              Depth                    :   22
%              Number of atoms          :  293 (18301 expanded)
%              Number of equality atoms :  113 (4891 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f268,plain,(
    $false ),
    inference(global_subsumption,[],[f41,f241,f242,f267])).

fof(f267,plain,(
    k1_xboole_0 = k1_relat_1(sK4) ),
    inference(backward_demodulation,[],[f250,f266])).

fof(f266,plain,(
    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) ),
    inference(subsumption_resolution,[],[f263,f244])).

fof(f244,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f201,f217])).

fof(f217,plain,(
    k1_xboole_0 = sK1 ),
    inference(global_subsumption,[],[f42,f199])).

fof(f199,plain,(
    k1_xboole_0 = sK2 ),
    inference(global_subsumption,[],[f41,f191,f196,f197])).

fof(f197,plain,
    ( sK1 = k1_relat_1(sK4)
    | k1_xboole_0 = sK2 ),
    inference(superposition,[],[f115,f87])).

fof(f87,plain,
    ( sK1 = k1_relset_1(sK1,sK2,sK4)
    | k1_xboole_0 = sK2 ),
    inference(subsumption_resolution,[],[f86,f45])).

fof(f45,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ v2_funct_1(X4)
            | ~ v2_funct_1(X3) )
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & k2_relset_1(X0,X1,X3) = X1
          & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( ( ~ v2_funct_1(X4)
            | ~ v2_funct_1(X3) )
          & ( k1_xboole_0 = X1
            | k1_xboole_0 != X2 )
          & k2_relset_1(X0,X1,X3) = X1
          & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( k2_relset_1(X0,X1,X3) = X1
                & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
             => ( ( v2_funct_1(X4)
                  & v2_funct_1(X3) )
                | ( k1_xboole_0 != X1
                  & k1_xboole_0 = X2 ) ) ) ) ) ),
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X0,X1,X3) = X1
              & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) )
           => ( ( v2_funct_1(X4)
                & v2_funct_1(X3) )
              | ( k1_xboole_0 != X1
                & k1_xboole_0 = X2 ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

fof(f86,plain,
    ( k1_xboole_0 = sK2
    | sK1 = k1_relset_1(sK1,sK2,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(resolution,[],[f44,f56])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( v1_funct_2(X2,X0,X1)
          <=> k1_xboole_0 = X2 )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( k1_xboole_0 = X1
         => ( ( v1_funct_2(X2,X0,X1)
            <=> k1_xboole_0 = X2 )
            | k1_xboole_0 = X0 ) )
        & ( ( k1_xboole_0 = X1
           => k1_xboole_0 = X0 )
         => ( v1_funct_2(X2,X0,X1)
          <=> k1_relset_1(X0,X1,X2) = X0 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f44,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f115,plain,(
    k1_relat_1(sK4) = k1_relset_1(sK1,sK2,sK4) ),
    inference(backward_demodulation,[],[f106,f113])).

fof(f113,plain,(
    k1_relat_1(sK4) = k10_relat_1(sK4,sK2) ),
    inference(backward_demodulation,[],[f109,f110])).

fof(f110,plain,(
    k1_relat_1(sK4) = k10_relat_1(sK4,k2_relat_1(sK4)) ),
    inference(resolution,[],[f97,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f97,plain,(
    v1_relat_1(sK4) ),
    inference(resolution,[],[f45,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f109,plain,(
    k10_relat_1(sK4,sK2) = k10_relat_1(sK4,k2_relat_1(sK4)) ),
    inference(forward_demodulation,[],[f107,f106])).

fof(f107,plain,(
    k1_relset_1(sK1,sK2,sK4) = k10_relat_1(sK4,k2_relat_1(sK4)) ),
    inference(backward_demodulation,[],[f103,f99])).

fof(f99,plain,(
    ! [X3] : k8_relset_1(sK1,sK2,sK4,X3) = k10_relat_1(sK4,X3) ),
    inference(resolution,[],[f45,f75])).

fof(f75,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f103,plain,(
    k1_relset_1(sK1,sK2,sK4) = k8_relset_1(sK1,sK2,sK4,k2_relat_1(sK4)) ),
    inference(backward_demodulation,[],[f100,f95])).

fof(f95,plain,(
    k2_relat_1(sK4) = k2_relset_1(sK1,sK2,sK4) ),
    inference(resolution,[],[f45,f64])).

fof(f64,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f100,plain,(
    k1_relset_1(sK1,sK2,sK4) = k8_relset_1(sK1,sK2,sK4,k2_relset_1(sK1,sK2,sK4)) ),
    inference(backward_demodulation,[],[f92,f93])).

fof(f93,plain,(
    k2_relset_1(sK1,sK2,sK4) = k7_relset_1(sK1,sK2,sK4,sK1) ),
    inference(resolution,[],[f45,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f92,plain,(
    k1_relset_1(sK1,sK2,sK4) = k8_relset_1(sK1,sK2,sK4,k7_relset_1(sK1,sK2,sK4,sK1)) ),
    inference(resolution,[],[f45,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
     => ( k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)
        & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).

fof(f106,plain,(
    k1_relset_1(sK1,sK2,sK4) = k10_relat_1(sK4,sK2) ),
    inference(backward_demodulation,[],[f94,f99])).

fof(f94,plain,(
    k1_relset_1(sK1,sK2,sK4) = k8_relset_1(sK1,sK2,sK4,sK2) ),
    inference(resolution,[],[f45,f63])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f196,plain,
    ( sK1 != k1_relat_1(sK4)
    | v2_funct_1(sK4) ),
    inference(forward_demodulation,[],[f195,f130])).

fof(f130,plain,(
    sK1 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f121,f47])).

fof(f47,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f121,plain,(
    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f50,f64])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f195,plain,
    ( k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f194,f97])).

fof(f194,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f193,f48])).

fof(f48,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f193,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f192,f123])).

fof(f123,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f50,f68])).

fof(f192,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK4) ),
    inference(subsumption_resolution,[],[f186,f43])).

fof(f43,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f23])).

fof(f186,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK4) ),
    inference(resolution,[],[f182,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | v2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

% (31083)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% (31095)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% (31087)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% (31092)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% (31074)Refutation not found, incomplete strategy% (31074)------------------------------
% (31074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (31074)Termination reason: Refutation not found, incomplete strategy

% (31074)Memory used [KB]: 10746
% (31074)Time elapsed: 0.197 s
% (31074)------------------------------
% (31074)------------------------------
fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(f182,plain,(
    v2_funct_1(k5_relat_1(sK3,sK4)) ),
    inference(backward_demodulation,[],[f46,f181])).

fof(f181,plain,(
    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(subsumption_resolution,[],[f178,f43])).

fof(f178,plain,
    ( ~ v1_funct_1(sK4)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    inference(resolution,[],[f133,f45])).

fof(f133,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_1(X0)
      | k1_partfun1(sK0,sK1,X1,X2,sK3,X0) = k5_relat_1(sK3,X0) ) ),
    inference(subsumption_resolution,[],[f122,f48])).

fof(f122,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(sK3)
      | ~ v1_funct_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_partfun1(sK0,sK1,X1,X2,sK3,X0) = k5_relat_1(sK3,X0) ) ),
    inference(resolution,[],[f50,f67])).

fof(f67,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f46,plain,(
    v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f23])).

fof(f191,plain,
    ( sK1 != k1_relat_1(sK4)
    | v2_funct_1(sK3) ),
    inference(forward_demodulation,[],[f190,f130])).

fof(f190,plain,
    ( k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f189,f97])).

fof(f189,plain,
    ( ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f188,f48])).

fof(f188,plain,
    ( ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f187,f123])).

fof(f187,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f185,f43])).

fof(f185,plain,
    ( ~ v1_funct_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK4)
    | k1_relat_1(sK4) != k2_relat_1(sK3)
    | v2_funct_1(sK3) ),
    inference(resolution,[],[f182,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k5_relat_1(X1,X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X1) != k1_relat_1(X0)
      | v2_funct_1(X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f42,plain,
    ( k1_xboole_0 != sK2
    | k1_xboole_0 = sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f201,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    inference(backward_demodulation,[],[f45,f199])).

fof(f263,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    inference(resolution,[],[f243,f77])).

fof(f77,plain,(
    ! [X2,X1] :
      ( ~ v1_funct_2(X2,k1_xboole_0,X1)
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) ) ),
    inference(equality_resolution,[],[f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f243,plain,(
    v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) ),
    inference(backward_demodulation,[],[f200,f217])).

fof(f200,plain,(
    v1_funct_2(sK4,sK1,k1_xboole_0) ),
    inference(backward_demodulation,[],[f44,f199])).

fof(f250,plain,(
    k1_relat_1(sK4) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) ),
    inference(backward_demodulation,[],[f208,f217])).

fof(f208,plain,(
    k1_relat_1(sK4) = k1_relset_1(sK1,k1_xboole_0,sK4) ),
    inference(backward_demodulation,[],[f115,f199])).

fof(f242,plain,
    ( k1_xboole_0 != k1_relat_1(sK4)
    | v2_funct_1(sK4) ),
    inference(backward_demodulation,[],[f196,f217])).

fof(f241,plain,
    ( k1_xboole_0 != k1_relat_1(sK4)
    | v2_funct_1(sK3) ),
    inference(backward_demodulation,[],[f191,f217])).

fof(f41,plain,
    ( ~ v2_funct_1(sK4)
    | ~ v2_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % WCLimit    : 600
% 0.12/0.34  % DateTime   : Tue Dec  1 14:17:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.19/0.51  % (31089)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.19/0.51  % (31088)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.19/0.52  % (31080)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.19/0.52  % (31076)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.19/0.52  % (31081)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.19/0.53  % (31097)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.19/0.54  % (31080)Refutation not found, incomplete strategy% (31080)------------------------------
% 0.19/0.54  % (31080)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.19/0.54  % (31080)Termination reason: Refutation not found, incomplete strategy
% 0.19/0.54  
% 0.19/0.54  % (31080)Memory used [KB]: 10746
% 0.19/0.54  % (31080)Time elapsed: 0.106 s
% 0.19/0.54  % (31080)------------------------------
% 0.19/0.54  % (31080)------------------------------
% 0.19/0.55  % (31078)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.19/0.55  % (31077)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 1.48/0.56  % (31081)Refutation not found, incomplete strategy% (31081)------------------------------
% 1.48/0.56  % (31081)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.48/0.56  % (31081)Termination reason: Refutation not found, incomplete strategy
% 1.48/0.56  
% 1.48/0.56  % (31081)Memory used [KB]: 1918
% 1.48/0.56  % (31081)Time elapsed: 0.127 s
% 1.48/0.56  % (31081)------------------------------
% 1.48/0.56  % (31081)------------------------------
% 1.48/0.57  % (31079)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 1.48/0.57  % (31094)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 1.48/0.57  % (31075)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 1.48/0.57  % (31093)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 1.48/0.58  % (31099)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 1.48/0.58  % (31086)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 1.84/0.58  % (31090)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 1.84/0.59  % (31085)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 1.84/0.59  % (31074)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 1.84/0.59  % (31091)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.84/0.59  % (31082)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.84/0.59  % (31098)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 1.84/0.59  % (31079)Refutation found. Thanks to Tanya!
% 1.84/0.59  % SZS status Theorem for theBenchmark
% 1.84/0.59  % SZS output start Proof for theBenchmark
% 1.84/0.59  fof(f268,plain,(
% 1.84/0.59    $false),
% 1.84/0.59    inference(global_subsumption,[],[f41,f241,f242,f267])).
% 1.84/0.59  fof(f267,plain,(
% 1.84/0.59    k1_xboole_0 = k1_relat_1(sK4)),
% 1.84/0.59    inference(backward_demodulation,[],[f250,f266])).
% 1.84/0.59  fof(f266,plain,(
% 1.84/0.59    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)),
% 1.84/0.59    inference(subsumption_resolution,[],[f263,f244])).
% 1.84/0.59  fof(f244,plain,(
% 1.84/0.59    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.84/0.59    inference(backward_demodulation,[],[f201,f217])).
% 1.84/0.59  fof(f217,plain,(
% 1.84/0.59    k1_xboole_0 = sK1),
% 1.84/0.59    inference(global_subsumption,[],[f42,f199])).
% 1.84/0.59  fof(f199,plain,(
% 1.84/0.59    k1_xboole_0 = sK2),
% 1.84/0.59    inference(global_subsumption,[],[f41,f191,f196,f197])).
% 1.84/0.59  fof(f197,plain,(
% 1.84/0.59    sK1 = k1_relat_1(sK4) | k1_xboole_0 = sK2),
% 1.84/0.59    inference(superposition,[],[f115,f87])).
% 1.84/0.59  fof(f87,plain,(
% 1.84/0.59    sK1 = k1_relset_1(sK1,sK2,sK4) | k1_xboole_0 = sK2),
% 1.84/0.59    inference(subsumption_resolution,[],[f86,f45])).
% 1.84/0.59  fof(f45,plain,(
% 1.84/0.59    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.84/0.59    inference(cnf_transformation,[],[f23])).
% 1.84/0.59  fof(f23,plain,(
% 1.84/0.59    ? [X0,X1,X2,X3] : (? [X4] : ((~v2_funct_1(X4) | ~v2_funct_1(X3)) & (k1_xboole_0 = X1 | k1_xboole_0 != X2) & k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3))),
% 1.84/0.59    inference(flattening,[],[f22])).
% 1.84/0.59  fof(f22,plain,(
% 1.84/0.59    ? [X0,X1,X2,X3] : (? [X4] : ((((~v2_funct_1(X4) | ~v2_funct_1(X3)) & (k1_xboole_0 = X1 | k1_xboole_0 != X2)) & (k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4))) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)))),
% 1.84/0.59    inference(ennf_transformation,[],[f21])).
% 1.84/0.59  fof(f21,negated_conjecture,(
% 1.84/0.59    ~! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.84/0.59    inference(negated_conjecture,[],[f20])).
% 1.84/0.59  fof(f20,conjecture,(
% 1.84/0.59    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 1.84/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 1.84/0.59  fof(f86,plain,(
% 1.84/0.59    k1_xboole_0 = sK2 | sK1 = k1_relset_1(sK1,sK2,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))),
% 1.84/0.59    inference(resolution,[],[f44,f56])).
% 1.84/0.59  fof(f56,plain,(
% 1.84/0.59    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.84/0.59    inference(cnf_transformation,[],[f25])).
% 1.84/0.59  fof(f25,plain,(
% 1.84/0.59    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/0.59    inference(flattening,[],[f24])).
% 1.84/0.59  fof(f24,plain,(
% 1.84/0.59    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/0.59    inference(ennf_transformation,[],[f17])).
% 1.84/0.59  fof(f17,axiom,(
% 1.84/0.59    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 1.84/0.59    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 1.84/0.59  fof(f44,plain,(
% 1.84/0.59    v1_funct_2(sK4,sK1,sK2)),
% 1.84/0.59    inference(cnf_transformation,[],[f23])).
% 1.84/0.59  fof(f115,plain,(
% 1.84/0.59    k1_relat_1(sK4) = k1_relset_1(sK1,sK2,sK4)),
% 1.84/0.59    inference(backward_demodulation,[],[f106,f113])).
% 1.84/0.59  fof(f113,plain,(
% 1.84/0.59    k1_relat_1(sK4) = k10_relat_1(sK4,sK2)),
% 1.84/0.59    inference(backward_demodulation,[],[f109,f110])).
% 1.84/0.59  fof(f110,plain,(
% 1.84/0.59    k1_relat_1(sK4) = k10_relat_1(sK4,k2_relat_1(sK4))),
% 1.84/0.59    inference(resolution,[],[f97,f76])).
% 1.84/0.60  fof(f76,plain,(
% 1.84/0.60    ( ! [X0] : (~v1_relat_1(X0) | k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f40])).
% 1.84/0.60  fof(f40,plain,(
% 1.84/0.60    ! [X0] : (k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0) | ~v1_relat_1(X0))),
% 1.84/0.60    inference(ennf_transformation,[],[f7])).
% 1.84/0.60  fof(f7,axiom,(
% 1.84/0.60    ! [X0] : (v1_relat_1(X0) => k10_relat_1(X0,k2_relat_1(X0)) = k1_relat_1(X0))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 1.84/0.60  fof(f97,plain,(
% 1.84/0.60    v1_relat_1(sK4)),
% 1.84/0.60    inference(resolution,[],[f45,f68])).
% 1.84/0.60  fof(f68,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f34])).
% 1.84/0.60  fof(f34,plain,(
% 1.84/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/0.60    inference(ennf_transformation,[],[f10])).
% 1.84/0.60  fof(f10,axiom,(
% 1.84/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.84/0.60  fof(f109,plain,(
% 1.84/0.60    k10_relat_1(sK4,sK2) = k10_relat_1(sK4,k2_relat_1(sK4))),
% 1.84/0.60    inference(forward_demodulation,[],[f107,f106])).
% 1.84/0.60  fof(f107,plain,(
% 1.84/0.60    k1_relset_1(sK1,sK2,sK4) = k10_relat_1(sK4,k2_relat_1(sK4))),
% 1.84/0.60    inference(backward_demodulation,[],[f103,f99])).
% 1.84/0.60  fof(f99,plain,(
% 1.84/0.60    ( ! [X3] : (k8_relset_1(sK1,sK2,sK4,X3) = k10_relat_1(sK4,X3)) )),
% 1.84/0.60    inference(resolution,[],[f45,f75])).
% 1.84/0.60  fof(f75,plain,(
% 1.84/0.60    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f39])).
% 1.84/0.60  fof(f39,plain,(
% 1.84/0.60    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/0.60    inference(ennf_transformation,[],[f14])).
% 1.84/0.60  fof(f14,axiom,(
% 1.84/0.60    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 1.84/0.60  fof(f103,plain,(
% 1.84/0.60    k1_relset_1(sK1,sK2,sK4) = k8_relset_1(sK1,sK2,sK4,k2_relat_1(sK4))),
% 1.84/0.60    inference(backward_demodulation,[],[f100,f95])).
% 1.84/0.60  fof(f95,plain,(
% 1.84/0.60    k2_relat_1(sK4) = k2_relset_1(sK1,sK2,sK4)),
% 1.84/0.60    inference(resolution,[],[f45,f64])).
% 1.84/0.60  fof(f64,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f29])).
% 1.84/0.60  fof(f29,plain,(
% 1.84/0.60    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/0.60    inference(ennf_transformation,[],[f13])).
% 1.84/0.60  fof(f13,axiom,(
% 1.84/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.84/0.60  fof(f100,plain,(
% 1.84/0.60    k1_relset_1(sK1,sK2,sK4) = k8_relset_1(sK1,sK2,sK4,k2_relset_1(sK1,sK2,sK4))),
% 1.84/0.60    inference(backward_demodulation,[],[f92,f93])).
% 1.84/0.60  fof(f93,plain,(
% 1.84/0.60    k2_relset_1(sK1,sK2,sK4) = k7_relset_1(sK1,sK2,sK4,sK1)),
% 1.84/0.60    inference(resolution,[],[f45,f62])).
% 1.84/0.60  fof(f62,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f28])).
% 1.84/0.60  fof(f28,plain,(
% 1.84/0.60    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.84/0.60    inference(ennf_transformation,[],[f15])).
% 1.84/0.60  fof(f15,axiom,(
% 1.84/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 1.84/0.60  fof(f92,plain,(
% 1.84/0.60    k1_relset_1(sK1,sK2,sK4) = k8_relset_1(sK1,sK2,sK4,k7_relset_1(sK1,sK2,sK4,sK1))),
% 1.84/0.60    inference(resolution,[],[f45,f61])).
% 1.84/0.60  fof(f61,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f27])).
% 1.84/0.60  fof(f27,plain,(
% 1.84/0.60    ! [X0,X1,X2] : ((k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.84/0.60    inference(ennf_transformation,[],[f16])).
% 1.84/0.60  fof(f16,axiom,(
% 1.84/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) => (k8_relset_1(X1,X0,X2,k7_relset_1(X1,X0,X2,X1)) = k1_relset_1(X1,X0,X2) & k7_relset_1(X1,X0,X2,k8_relset_1(X1,X0,X2,X0)) = k2_relset_1(X1,X0,X2)))),
% 1.84/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_relset_1)).
% 1.84/0.60  fof(f106,plain,(
% 1.84/0.60    k1_relset_1(sK1,sK2,sK4) = k10_relat_1(sK4,sK2)),
% 1.84/0.60    inference(backward_demodulation,[],[f94,f99])).
% 1.84/0.60  fof(f94,plain,(
% 1.84/0.60    k1_relset_1(sK1,sK2,sK4) = k8_relset_1(sK1,sK2,sK4,sK2)),
% 1.84/0.60    inference(resolution,[],[f45,f63])).
% 1.84/0.60  fof(f63,plain,(
% 1.84/0.60    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f28])).
% 1.84/0.60  fof(f196,plain,(
% 1.84/0.60    sK1 != k1_relat_1(sK4) | v2_funct_1(sK4)),
% 1.84/0.60    inference(forward_demodulation,[],[f195,f130])).
% 1.84/0.60  fof(f130,plain,(
% 1.84/0.60    sK1 = k2_relat_1(sK3)),
% 1.84/0.60    inference(forward_demodulation,[],[f121,f47])).
% 1.84/0.60  fof(f47,plain,(
% 1.84/0.60    sK1 = k2_relset_1(sK0,sK1,sK3)),
% 1.84/0.60    inference(cnf_transformation,[],[f23])).
% 1.84/0.60  fof(f121,plain,(
% 1.84/0.60    k2_relset_1(sK0,sK1,sK3) = k2_relat_1(sK3)),
% 1.84/0.60    inference(resolution,[],[f50,f64])).
% 1.84/0.60  fof(f50,plain,(
% 1.84/0.60    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.84/0.60    inference(cnf_transformation,[],[f23])).
% 1.84/0.60  fof(f195,plain,(
% 1.84/0.60    k1_relat_1(sK4) != k2_relat_1(sK3) | v2_funct_1(sK4)),
% 1.84/0.60    inference(subsumption_resolution,[],[f194,f97])).
% 1.84/0.60  fof(f194,plain,(
% 1.84/0.60    ~v1_relat_1(sK4) | k1_relat_1(sK4) != k2_relat_1(sK3) | v2_funct_1(sK4)),
% 1.84/0.60    inference(subsumption_resolution,[],[f193,f48])).
% 1.84/0.60  fof(f48,plain,(
% 1.84/0.60    v1_funct_1(sK3)),
% 1.84/0.60    inference(cnf_transformation,[],[f23])).
% 1.84/0.60  fof(f193,plain,(
% 1.84/0.60    ~v1_funct_1(sK3) | ~v1_relat_1(sK4) | k1_relat_1(sK4) != k2_relat_1(sK3) | v2_funct_1(sK4)),
% 1.84/0.60    inference(subsumption_resolution,[],[f192,f123])).
% 1.84/0.60  fof(f123,plain,(
% 1.84/0.60    v1_relat_1(sK3)),
% 1.84/0.60    inference(resolution,[],[f50,f68])).
% 1.84/0.60  fof(f192,plain,(
% 1.84/0.60    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK4) | k1_relat_1(sK4) != k2_relat_1(sK3) | v2_funct_1(sK4)),
% 1.84/0.60    inference(subsumption_resolution,[],[f186,f43])).
% 1.84/0.60  fof(f43,plain,(
% 1.84/0.60    v1_funct_1(sK4)),
% 1.84/0.60    inference(cnf_transformation,[],[f23])).
% 1.84/0.60  fof(f186,plain,(
% 1.84/0.60    ~v1_funct_1(sK4) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK4) | k1_relat_1(sK4) != k2_relat_1(sK3) | v2_funct_1(sK4)),
% 1.84/0.60    inference(resolution,[],[f182,f66])).
% 1.84/0.60  fof(f66,plain,(
% 1.84/0.60    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | v2_funct_1(X0)) )),
% 1.84/0.60    inference(cnf_transformation,[],[f31])).
% 1.84/0.60  fof(f31,plain,(
% 1.84/0.60    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.84/0.60    inference(flattening,[],[f30])).
% 1.84/0.60  fof(f30,plain,(
% 1.84/0.60    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.84/0.60    inference(ennf_transformation,[],[f9])).
% 1.84/0.60  % (31083)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.84/0.60  % (31095)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.84/0.60  % (31087)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 1.84/0.61  % (31092)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 1.84/0.62  % (31074)Refutation not found, incomplete strategy% (31074)------------------------------
% 1.84/0.62  % (31074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.62  % (31074)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.62  
% 1.84/0.62  % (31074)Memory used [KB]: 10746
% 1.84/0.62  % (31074)Time elapsed: 0.197 s
% 1.84/0.62  % (31074)------------------------------
% 1.84/0.62  % (31074)------------------------------
% 1.84/0.62  fof(f9,axiom,(
% 1.84/0.62    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 1.84/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 1.84/0.62  fof(f182,plain,(
% 1.84/0.62    v2_funct_1(k5_relat_1(sK3,sK4))),
% 1.84/0.62    inference(backward_demodulation,[],[f46,f181])).
% 1.84/0.62  fof(f181,plain,(
% 1.84/0.62    k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 1.84/0.62    inference(subsumption_resolution,[],[f178,f43])).
% 1.84/0.62  fof(f178,plain,(
% 1.84/0.62    ~v1_funct_1(sK4) | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)),
% 1.84/0.62    inference(resolution,[],[f133,f45])).
% 1.84/0.62  fof(f133,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_1(X0) | k1_partfun1(sK0,sK1,X1,X2,sK3,X0) = k5_relat_1(sK3,X0)) )),
% 1.84/0.62    inference(subsumption_resolution,[],[f122,f48])).
% 1.84/0.62  fof(f122,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (~v1_funct_1(sK3) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_partfun1(sK0,sK1,X1,X2,sK3,X0) = k5_relat_1(sK3,X0)) )),
% 1.84/0.62    inference(resolution,[],[f50,f67])).
% 1.84/0.62  fof(f67,plain,(
% 1.84/0.62    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 1.84/0.62    inference(cnf_transformation,[],[f33])).
% 1.84/0.62  fof(f33,plain,(
% 1.84/0.62    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.84/0.62    inference(flattening,[],[f32])).
% 1.84/0.62  fof(f32,plain,(
% 1.84/0.62    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.84/0.62    inference(ennf_transformation,[],[f18])).
% 1.84/0.62  fof(f18,axiom,(
% 1.84/0.62    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.84/0.62    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.84/0.62  fof(f46,plain,(
% 1.84/0.62    v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))),
% 1.84/0.62    inference(cnf_transformation,[],[f23])).
% 1.84/0.62  fof(f191,plain,(
% 1.84/0.62    sK1 != k1_relat_1(sK4) | v2_funct_1(sK3)),
% 1.84/0.62    inference(forward_demodulation,[],[f190,f130])).
% 1.84/0.62  fof(f190,plain,(
% 1.84/0.62    k1_relat_1(sK4) != k2_relat_1(sK3) | v2_funct_1(sK3)),
% 1.84/0.62    inference(subsumption_resolution,[],[f189,f97])).
% 1.84/0.62  fof(f189,plain,(
% 1.84/0.62    ~v1_relat_1(sK4) | k1_relat_1(sK4) != k2_relat_1(sK3) | v2_funct_1(sK3)),
% 1.84/0.62    inference(subsumption_resolution,[],[f188,f48])).
% 1.84/0.62  fof(f188,plain,(
% 1.84/0.62    ~v1_funct_1(sK3) | ~v1_relat_1(sK4) | k1_relat_1(sK4) != k2_relat_1(sK3) | v2_funct_1(sK3)),
% 1.84/0.62    inference(subsumption_resolution,[],[f187,f123])).
% 1.84/0.62  fof(f187,plain,(
% 1.84/0.62    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK4) | k1_relat_1(sK4) != k2_relat_1(sK3) | v2_funct_1(sK3)),
% 1.84/0.62    inference(subsumption_resolution,[],[f185,f43])).
% 1.84/0.62  fof(f185,plain,(
% 1.84/0.62    ~v1_funct_1(sK4) | ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK4) | k1_relat_1(sK4) != k2_relat_1(sK3) | v2_funct_1(sK3)),
% 1.84/0.62    inference(resolution,[],[f182,f65])).
% 1.84/0.62  fof(f65,plain,(
% 1.84/0.62    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X0) | k2_relat_1(X1) != k1_relat_1(X0) | v2_funct_1(X1)) )),
% 1.84/0.62    inference(cnf_transformation,[],[f31])).
% 1.84/0.62  fof(f42,plain,(
% 1.84/0.62    k1_xboole_0 != sK2 | k1_xboole_0 = sK1),
% 1.84/0.62    inference(cnf_transformation,[],[f23])).
% 1.84/0.62  fof(f201,plain,(
% 1.84/0.62    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))),
% 1.84/0.62    inference(backward_demodulation,[],[f45,f199])).
% 1.84/0.62  fof(f263,plain,(
% 1.84/0.62    k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))),
% 1.84/0.62    inference(resolution,[],[f243,f77])).
% 1.84/0.62  fof(f77,plain,(
% 1.84/0.62    ( ! [X2,X1] : (~v1_funct_2(X2,k1_xboole_0,X1) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))) )),
% 1.84/0.62    inference(equality_resolution,[],[f54])).
% 1.84/0.62  fof(f54,plain,(
% 1.84/0.62    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 1.84/0.62    inference(cnf_transformation,[],[f25])).
% 1.84/0.62  fof(f243,plain,(
% 1.84/0.62    v1_funct_2(sK4,k1_xboole_0,k1_xboole_0)),
% 1.84/0.62    inference(backward_demodulation,[],[f200,f217])).
% 1.84/0.62  fof(f200,plain,(
% 1.84/0.62    v1_funct_2(sK4,sK1,k1_xboole_0)),
% 1.84/0.62    inference(backward_demodulation,[],[f44,f199])).
% 1.84/0.62  fof(f250,plain,(
% 1.84/0.62    k1_relat_1(sK4) = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)),
% 1.84/0.62    inference(backward_demodulation,[],[f208,f217])).
% 1.84/0.62  fof(f208,plain,(
% 1.84/0.62    k1_relat_1(sK4) = k1_relset_1(sK1,k1_xboole_0,sK4)),
% 1.84/0.62    inference(backward_demodulation,[],[f115,f199])).
% 1.84/0.62  fof(f242,plain,(
% 1.84/0.62    k1_xboole_0 != k1_relat_1(sK4) | v2_funct_1(sK4)),
% 1.84/0.62    inference(backward_demodulation,[],[f196,f217])).
% 1.84/0.62  fof(f241,plain,(
% 1.84/0.62    k1_xboole_0 != k1_relat_1(sK4) | v2_funct_1(sK3)),
% 1.84/0.62    inference(backward_demodulation,[],[f191,f217])).
% 1.84/0.62  fof(f41,plain,(
% 1.84/0.62    ~v2_funct_1(sK4) | ~v2_funct_1(sK3)),
% 1.84/0.62    inference(cnf_transformation,[],[f23])).
% 1.84/0.62  % SZS output end Proof for theBenchmark
% 1.84/0.62  % (31079)------------------------------
% 1.84/0.62  % (31079)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.62  % (31079)Termination reason: Refutation
% 1.84/0.62  
% 1.84/0.62  % (31079)Memory used [KB]: 6396
% 1.84/0.62  % (31079)Time elapsed: 0.174 s
% 1.84/0.62  % (31079)------------------------------
% 1.84/0.62  % (31079)------------------------------
% 1.84/0.62  % (31073)Success in time 0.27 s
%------------------------------------------------------------------------------
