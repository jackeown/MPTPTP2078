%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:28 EST 2020

% Result     : Theorem 1.93s
% Output     : Refutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :  203 (3626 expanded)
%              Number of leaves         :   20 ( 674 expanded)
%              Depth                    :   31
%              Number of atoms          :  572 (25873 expanded)
%              Number of equality atoms :  196 (8353 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2662,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2661,f396])).

fof(f396,plain,(
    sK3 != k4_relat_1(sK2) ),
    inference(superposition,[],[f60,f354])).

fof(f354,plain,(
    k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(resolution,[],[f130,f248])).

fof(f248,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f63,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f63,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ? [X0,X1,X2] :
      ( ? [X3] :
          ( k2_funct_1(X2) != X3
          & k1_xboole_0 != X1
          & k1_xboole_0 != X0
          & v2_funct_1(X2)
          & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
          & k2_relset_1(X0,X1,X2) = X1
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(X3,X1,X0)
          & v1_funct_1(X3) )
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ! [X3] :
            ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
              & v1_funct_2(X3,X1,X0)
              & v1_funct_1(X3) )
           => ( ( v2_funct_1(X2)
                & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
                & k2_relset_1(X0,X1,X2) = X1 )
             => ( k2_funct_1(X2) = X3
                | k1_xboole_0 = X1
                | k1_xboole_0 = X0 ) ) ) ) ),
    inference(negated_conjecture,[],[f22])).

fof(f22,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( ( v2_funct_1(X2)
              & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0))
              & k2_relset_1(X0,X1,X2) = X1 )
           => ( k2_funct_1(X2) = X3
              | k1_xboole_0 = X1
              | k1_xboole_0 = X0 ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f130,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f123,f61])).

fof(f61,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f123,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(resolution,[],[f57,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f57,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f60,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f2661,plain,(
    sK3 = k4_relat_1(sK2) ),
    inference(backward_demodulation,[],[f2596,f2660])).

fof(f2660,plain,(
    sK3 = k5_relat_1(sK3,k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f2534,f1879])).

fof(f1879,plain,(
    sK3 = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(backward_demodulation,[],[f219,f1873])).

fof(f1873,plain,(
    sK1 = k1_relat_1(sK3) ),
    inference(resolution,[],[f1620,f243])).

fof(f243,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(sK3))
    | sK1 = k1_relat_1(sK3) ),
    inference(resolution,[],[f221,f87])).

fof(f87,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f221,plain,(
    r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(subsumption_resolution,[],[f220,f182])).

fof(f182,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f54,f88])).

fof(f54,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f25])).

fof(f220,plain,
    ( ~ v1_relat_1(sK3)
    | r1_tarski(k1_relat_1(sK3),sK1) ),
    inference(resolution,[],[f183,f84])).

fof(f84,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | r1_tarski(k1_relat_1(X1),X0)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).

fof(f183,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f54,f89])).

fof(f89,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f1620,plain,(
    r1_tarski(sK1,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f1578,f99])).

fof(f99,plain,(
    ! [X0] : k1_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f67,f64])).

fof(f64,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f67,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1578,plain,
    ( sK0 != k1_relat_1(k6_partfun1(sK0))
    | r1_tarski(sK1,k1_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f490,f1555])).

fof(f1555,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f1554,f1042])).

fof(f1042,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(forward_demodulation,[],[f1033,f1031])).

fof(f1031,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f1026,f61])).

fof(f1026,plain,
    ( ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f197,f63])).

fof(f197,plain,(
    ! [X6,X7,X5] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(X5)
      | k1_partfun1(X6,X7,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) ) ),
    inference(subsumption_resolution,[],[f190,f52])).

fof(f52,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f25])).

fof(f190,plain,(
    ! [X6,X7,X5] :
      ( ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
      | ~ v1_funct_1(sK3)
      | k1_partfun1(X6,X7,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3) ) ),
    inference(resolution,[],[f54,f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f1033,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(backward_demodulation,[],[f268,f1031])).

fof(f268,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(subsumption_resolution,[],[f266,f66])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f266,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(resolution,[],[f56,f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f56,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f25])).

fof(f1554,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f1553,f54])).

fof(f1553,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1552,f52])).

fof(f1552,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1551,f63])).

fof(f1551,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1550,f61])).

fof(f1550,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f97,f1031])).

fof(f97,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f490,plain,
    ( sK0 != k1_relat_1(k5_relat_1(sK2,sK3))
    | r1_tarski(sK1,k1_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f482,f182])).

fof(f482,plain,
    ( sK0 != k1_relat_1(k5_relat_1(sK2,sK3))
    | ~ v1_relat_1(sK3)
    | r1_tarski(sK1,k1_relat_1(sK3)) ),
    inference(resolution,[],[f333,f52])).

fof(f333,plain,(
    ! [X1] :
      ( ~ v1_funct_1(X1)
      | sK0 != k1_relat_1(k5_relat_1(sK2,X1))
      | ~ v1_relat_1(X1)
      | r1_tarski(sK1,k1_relat_1(X1)) ) ),
    inference(backward_demodulation,[],[f322,f331])).

fof(f331,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(resolution,[],[f179,f248])).

fof(f179,plain,
    ( ~ v1_relat_1(sK2)
    | sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f177,f98])).

fof(f98,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f68,f64])).

fof(f68,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f6])).

fof(f177,plain,
    ( k2_relat_1(sK2) = k2_relat_1(k6_partfun1(sK1))
    | ~ v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f132,f176])).

fof(f176,plain,(
    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f175,f59])).

fof(f59,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f25])).

fof(f175,plain,
    ( k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f174,f57])).

fof(f174,plain,
    ( ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f173,f55])).

fof(f55,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f25])).

fof(f173,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f172,f63])).

fof(f172,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(subsumption_resolution,[],[f162,f61])).

fof(f162,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1) ),
    inference(resolution,[],[f62,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f62,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f25])).

fof(f132,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) ),
    inference(subsumption_resolution,[],[f125,f61])).

fof(f125,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_relat_1(sK2) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2)) ),
    inference(resolution,[],[f57,f79])).

fof(f79,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
        & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))
          & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).

fof(f322,plain,(
    ! [X1] :
      ( sK0 != k1_relat_1(k5_relat_1(sK2,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | r1_tarski(k2_relat_1(sK2),k1_relat_1(X1)) ) ),
    inference(subsumption_resolution,[],[f317,f248])).

fof(f317,plain,(
    ! [X1] :
      ( sK0 != k1_relat_1(k5_relat_1(sK2,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(sK2)
      | r1_tarski(k2_relat_1(sK2),k1_relat_1(X1)) ) ),
    inference(backward_demodulation,[],[f143,f314])).

fof(f314,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(resolution,[],[f170,f248])).

fof(f170,plain,
    ( ~ v1_relat_1(sK2)
    | sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f168,f98])).

fof(f168,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK2) ),
    inference(backward_demodulation,[],[f134,f167])).

fof(f167,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f166,f59])).

fof(f166,plain,
    ( k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f165,f57])).

fof(f165,plain,
    ( ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f164,f55])).

fof(f164,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f163,f63])).

fof(f163,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f161,f61])).

fof(f161,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(resolution,[],[f62,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f134,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) ),
    inference(subsumption_resolution,[],[f127,f61])).

fof(f127,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2))) ),
    inference(resolution,[],[f57,f81])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
        & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))
          & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).

fof(f143,plain,(
    ! [X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(sK2)
      | k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,X1))
      | r1_tarski(k2_relat_1(sK2),k1_relat_1(X1)) ) ),
    inference(resolution,[],[f61,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
      | r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(X1),k1_relat_1(X0))
          | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0))
           => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).

fof(f219,plain,(
    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3) ),
    inference(resolution,[],[f182,f101])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(definition_unfolding,[],[f71,f64])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f2534,plain,(
    k5_relat_1(sK3,k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) ),
    inference(backward_demodulation,[],[f1579,f2476])).

fof(f2476,plain,(
    k6_partfun1(sK1) = k5_relat_1(sK3,sK2) ),
    inference(forward_demodulation,[],[f2475,f358])).

fof(f358,plain,(
    k6_partfun1(sK1) = k5_relat_1(k4_relat_1(sK2),sK2) ),
    inference(backward_demodulation,[],[f176,f354])).

fof(f2475,plain,(
    k5_relat_1(k4_relat_1(sK2),sK2) = k5_relat_1(sK3,sK2) ),
    inference(forward_demodulation,[],[f2474,f2409])).

fof(f2409,plain,(
    k5_relat_1(sK3,sK2) = k5_relat_1(k6_partfun1(sK1),k5_relat_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f1257,f2404])).

fof(f2404,plain,(
    sK1 = k1_relat_1(k5_relat_1(sK3,sK2)) ),
    inference(resolution,[],[f1540,f1635])).

fof(f1635,plain,(
    r1_tarski(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) ),
    inference(subsumption_resolution,[],[f1634,f1205])).

fof(f1205,plain,(
    v1_relat_1(k5_relat_1(sK3,sK2)) ),
    inference(resolution,[],[f1204,f88])).

fof(f1204,plain,(
    m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) ),
    inference(subsumption_resolution,[],[f1203,f63])).

fof(f1203,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1202,f61])).

fof(f1202,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1201,f54])).

fof(f1201,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(subsumption_resolution,[],[f1200,f52])).

fof(f1200,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(superposition,[],[f97,f878])).

fof(f878,plain,(
    k5_relat_1(sK3,sK2) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
    inference(subsumption_resolution,[],[f852,f61])).

fof(f852,plain,
    ( ~ v1_funct_1(sK2)
    | k5_relat_1(sK3,sK2) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2) ),
    inference(resolution,[],[f196,f63])).

fof(f196,plain,(
    ! [X4,X2,X3] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | ~ v1_funct_1(X2)
      | k1_partfun1(sK1,sK0,X3,X4,sK3,X2) = k5_relat_1(sK3,X2) ) ),
    inference(subsumption_resolution,[],[f189,f52])).

fof(f189,plain,(
    ! [X4,X2,X3] :
      ( ~ v1_funct_1(sK3)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
      | k1_partfun1(sK1,sK0,X3,X4,sK3,X2) = k5_relat_1(sK3,X2) ) ),
    inference(resolution,[],[f54,f95])).

fof(f1634,plain,
    ( r1_tarski(sK1,k1_relat_1(k5_relat_1(sK3,sK2)))
    | ~ v1_relat_1(k5_relat_1(sK3,sK2)) ),
    inference(subsumption_resolution,[],[f1622,f314])).

fof(f1622,plain,
    ( sK0 != k1_relat_1(sK2)
    | r1_tarski(sK1,k1_relat_1(k5_relat_1(sK3,sK2)))
    | ~ v1_relat_1(k5_relat_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f896,f1621])).

fof(f1621,plain,(
    sK2 = k5_relat_1(sK2,k5_relat_1(sK3,sK2)) ),
    inference(forward_demodulation,[],[f1585,f319])).

fof(f319,plain,(
    sK2 = k5_relat_1(k6_partfun1(sK0),sK2) ),
    inference(backward_demodulation,[],[f288,f314])).

fof(f288,plain,(
    sK2 = k5_relat_1(k6_partfun1(k1_relat_1(sK2)),sK2) ),
    inference(resolution,[],[f248,f101])).

fof(f1585,plain,(
    k5_relat_1(k6_partfun1(sK0),sK2) = k5_relat_1(sK2,k5_relat_1(sK3,sK2)) ),
    inference(backward_demodulation,[],[f695,f1555])).

fof(f695,plain,(
    k5_relat_1(k5_relat_1(sK2,sK3),sK2) = k5_relat_1(sK2,k5_relat_1(sK3,sK2)) ),
    inference(resolution,[],[f659,f248])).

fof(f659,plain,(
    ! [X11] :
      ( ~ v1_relat_1(X11)
      | k5_relat_1(k5_relat_1(sK2,sK3),X11) = k5_relat_1(sK2,k5_relat_1(sK3,X11)) ) ),
    inference(resolution,[],[f205,f248])).

fof(f205,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(X2,sK3),X3) = k5_relat_1(X2,k5_relat_1(sK3,X3)) ) ),
    inference(resolution,[],[f182,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f896,plain,
    ( r1_tarski(sK1,k1_relat_1(k5_relat_1(sK3,sK2)))
    | sK0 != k1_relat_1(k5_relat_1(sK2,k5_relat_1(sK3,sK2)))
    | ~ v1_relat_1(k5_relat_1(sK3,sK2)) ),
    inference(forward_demodulation,[],[f895,f878])).

fof(f895,plain,
    ( sK0 != k1_relat_1(k5_relat_1(sK2,k5_relat_1(sK3,sK2)))
    | ~ v1_relat_1(k5_relat_1(sK3,sK2))
    | r1_tarski(sK1,k1_relat_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2))) ),
    inference(forward_demodulation,[],[f884,f878])).

fof(f884,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,sK2))
    | sK0 != k1_relat_1(k5_relat_1(sK2,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)))
    | r1_tarski(sK1,k1_relat_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2))) ),
    inference(backward_demodulation,[],[f595,f878])).

fof(f595,plain,
    ( sK0 != k1_relat_1(k5_relat_1(sK2,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)))
    | ~ v1_relat_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2))
    | r1_tarski(sK1,k1_relat_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2))) ),
    inference(resolution,[],[f556,f333])).

fof(f556,plain,(
    v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)) ),
    inference(subsumption_resolution,[],[f553,f61])).

fof(f553,plain,
    ( ~ v1_funct_1(sK2)
    | v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)) ),
    inference(resolution,[],[f198,f63])).

fof(f198,plain,(
    ! [X10,X8,X9] :
      ( ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | ~ v1_funct_1(X8)
      | v1_funct_1(k1_partfun1(sK1,sK0,X9,X10,sK3,X8)) ) ),
    inference(subsumption_resolution,[],[f191,f52])).

fof(f191,plain,(
    ! [X10,X8,X9] :
      ( ~ v1_funct_1(sK3)
      | ~ v1_funct_1(X8)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X9,X10)))
      | v1_funct_1(k1_partfun1(sK1,sK0,X9,X10,sK3,X8)) ) ),
    inference(resolution,[],[f54,f96])).

fof(f96,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f1540,plain,
    ( ~ r1_tarski(sK1,k1_relat_1(k5_relat_1(sK3,sK2)))
    | sK1 = k1_relat_1(k5_relat_1(sK3,sK2)) ),
    inference(resolution,[],[f1355,f87])).

fof(f1355,plain,(
    r1_tarski(k1_relat_1(k5_relat_1(sK3,sK2)),sK1) ),
    inference(subsumption_resolution,[],[f1354,f1205])).

fof(f1354,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,sK2))
    | r1_tarski(k1_relat_1(k5_relat_1(sK3,sK2)),sK1) ),
    inference(resolution,[],[f1206,f84])).

fof(f1206,plain,(
    v4_relat_1(k5_relat_1(sK3,sK2),sK1) ),
    inference(resolution,[],[f1204,f89])).

fof(f1257,plain,(
    k5_relat_1(sK3,sK2) = k5_relat_1(k6_partfun1(k1_relat_1(k5_relat_1(sK3,sK2))),k5_relat_1(sK3,sK2)) ),
    inference(resolution,[],[f1205,f101])).

fof(f2474,plain,(
    k5_relat_1(k4_relat_1(sK2),sK2) = k5_relat_1(k6_partfun1(sK1),k5_relat_1(sK3,sK2)) ),
    inference(forward_demodulation,[],[f2459,f1621])).

fof(f2459,plain,(
    k5_relat_1(k6_partfun1(sK1),k5_relat_1(sK3,sK2)) = k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,k5_relat_1(sK3,sK2))) ),
    inference(resolution,[],[f848,f1205])).

fof(f848,plain,(
    ! [X6] :
      ( ~ v1_relat_1(X6)
      | k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,X6)) = k5_relat_1(k6_partfun1(sK1),X6) ) ),
    inference(forward_demodulation,[],[f842,f358])).

fof(f842,plain,(
    ! [X6] :
      ( ~ v1_relat_1(X6)
      | k5_relat_1(k5_relat_1(k4_relat_1(sK2),sK2),X6) = k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,X6)) ) ),
    inference(resolution,[],[f274,f359])).

fof(f359,plain,(
    v1_relat_1(k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f269,f354])).

fof(f269,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f248,f135])).

fof(f135,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f61,f75])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f274,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(X2,sK2),X3) = k5_relat_1(X2,k5_relat_1(sK2,X3)) ) ),
    inference(resolution,[],[f248,f74])).

fof(f1579,plain,(
    k5_relat_1(k5_relat_1(sK3,sK2),sK3) = k5_relat_1(sK3,k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f546,f1555])).

fof(f546,plain,(
    k5_relat_1(k5_relat_1(sK3,sK2),sK3) = k5_relat_1(sK3,k5_relat_1(sK2,sK3)) ),
    inference(resolution,[],[f537,f182])).

fof(f537,plain,(
    ! [X11] :
      ( ~ v1_relat_1(X11)
      | k5_relat_1(k5_relat_1(sK3,sK2),X11) = k5_relat_1(sK3,k5_relat_1(sK2,X11)) ) ),
    inference(resolution,[],[f204,f248])).

fof(f204,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(sK3,X0),X1) = k5_relat_1(sK3,k5_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f182,f74])).

fof(f2596,plain,(
    k4_relat_1(sK2) = k5_relat_1(sK3,k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f2482,f370])).

fof(f370,plain,(
    k4_relat_1(sK2) = k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f366,f335])).

fof(f335,plain,(
    sK1 = k1_relat_1(k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f271,f331])).

fof(f271,plain,(
    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(resolution,[],[f248,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f366,plain,(
    k4_relat_1(sK2) = k5_relat_1(k6_partfun1(k1_relat_1(k4_relat_1(sK2))),k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f309,f354])).

fof(f309,plain,(
    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK2))),k2_funct_1(sK2)) ),
    inference(resolution,[],[f269,f101])).

fof(f2482,plain,(
    k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2)) = k5_relat_1(sK3,k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f547,f2476])).

fof(f547,plain,(
    k5_relat_1(k5_relat_1(sK3,sK2),k4_relat_1(sK2)) = k5_relat_1(sK3,k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f541,f357])).

fof(f357,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f167,f354])).

fof(f541,plain,(
    k5_relat_1(k5_relat_1(sK3,sK2),k4_relat_1(sK2)) = k5_relat_1(sK3,k5_relat_1(sK2,k4_relat_1(sK2))) ),
    inference(resolution,[],[f537,f359])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n014.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 16:51:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (13780)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (13798)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.52  % (13782)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.53  % (13796)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.53  % (13790)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.53  % (13790)Refutation not found, incomplete strategy% (13790)------------------------------
% 0.21/0.53  % (13790)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.53  % (13790)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (13790)Memory used [KB]: 10746
% 0.21/0.53  % (13790)Time elapsed: 0.106 s
% 0.21/0.53  % (13790)------------------------------
% 0.21/0.53  % (13790)------------------------------
% 0.21/0.53  % (13781)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.54  % (13799)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.54  % (13788)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.55  % (13789)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.55  % (13791)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (13785)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.55  % (13779)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.55  % (13774)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.55  % (13775)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.55  % (13777)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.55  % (13783)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.56  % (13787)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.56  % (13786)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.56  % (13797)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.56  % (13795)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.56  % (13801)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.56  % (13802)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.56  % (13792)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.57  % (13803)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.57  % (13800)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.57  % (13784)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.57  % (13793)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.57  % (13778)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.58  % (13776)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 1.67/0.59  % (13794)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.93/0.63  % (13791)Refutation found. Thanks to Tanya!
% 1.93/0.63  % SZS status Theorem for theBenchmark
% 1.93/0.63  % SZS output start Proof for theBenchmark
% 1.93/0.63  fof(f2662,plain,(
% 1.93/0.63    $false),
% 1.93/0.63    inference(subsumption_resolution,[],[f2661,f396])).
% 1.93/0.63  fof(f396,plain,(
% 1.93/0.63    sK3 != k4_relat_1(sK2)),
% 1.93/0.63    inference(superposition,[],[f60,f354])).
% 1.93/0.63  fof(f354,plain,(
% 1.93/0.63    k2_funct_1(sK2) = k4_relat_1(sK2)),
% 1.93/0.63    inference(resolution,[],[f130,f248])).
% 1.93/0.63  fof(f248,plain,(
% 1.93/0.63    v1_relat_1(sK2)),
% 1.93/0.63    inference(resolution,[],[f63,f88])).
% 1.93/0.63  fof(f88,plain,(
% 1.93/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 1.93/0.63    inference(cnf_transformation,[],[f42])).
% 1.93/0.63  fof(f42,plain,(
% 1.93/0.63    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.93/0.63    inference(ennf_transformation,[],[f14])).
% 1.93/0.63  fof(f14,axiom,(
% 1.93/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.93/0.63  fof(f63,plain,(
% 1.93/0.63    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.93/0.63    inference(cnf_transformation,[],[f25])).
% 1.93/0.63  fof(f25,plain,(
% 1.93/0.63    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.93/0.63    inference(flattening,[],[f24])).
% 1.93/0.63  fof(f24,plain,(
% 1.93/0.63    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.93/0.63    inference(ennf_transformation,[],[f23])).
% 1.93/0.63  fof(f23,negated_conjecture,(
% 1.93/0.63    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.93/0.63    inference(negated_conjecture,[],[f22])).
% 1.93/0.63  fof(f22,conjecture,(
% 1.93/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.93/0.63  fof(f130,plain,(
% 1.93/0.63    ~v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2)),
% 1.93/0.63    inference(subsumption_resolution,[],[f123,f61])).
% 1.93/0.63  fof(f61,plain,(
% 1.93/0.63    v1_funct_1(sK2)),
% 1.93/0.63    inference(cnf_transformation,[],[f25])).
% 1.93/0.63  fof(f123,plain,(
% 1.93/0.63    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2)),
% 1.93/0.63    inference(resolution,[],[f57,f77])).
% 1.93/0.63  fof(f77,plain,(
% 1.93/0.63    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 1.93/0.63    inference(cnf_transformation,[],[f34])).
% 1.93/0.63  fof(f34,plain,(
% 1.93/0.63    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.93/0.63    inference(flattening,[],[f33])).
% 1.93/0.63  fof(f33,plain,(
% 1.93/0.63    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.93/0.63    inference(ennf_transformation,[],[f9])).
% 1.93/0.63  fof(f9,axiom,(
% 1.93/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 1.93/0.63  fof(f57,plain,(
% 1.93/0.63    v2_funct_1(sK2)),
% 1.93/0.63    inference(cnf_transformation,[],[f25])).
% 1.93/0.63  fof(f60,plain,(
% 1.93/0.63    sK3 != k2_funct_1(sK2)),
% 1.93/0.63    inference(cnf_transformation,[],[f25])).
% 1.93/0.63  fof(f2661,plain,(
% 1.93/0.63    sK3 = k4_relat_1(sK2)),
% 1.93/0.63    inference(backward_demodulation,[],[f2596,f2660])).
% 1.93/0.63  fof(f2660,plain,(
% 1.93/0.63    sK3 = k5_relat_1(sK3,k6_partfun1(sK0))),
% 1.93/0.63    inference(forward_demodulation,[],[f2534,f1879])).
% 1.93/0.63  fof(f1879,plain,(
% 1.93/0.63    sK3 = k5_relat_1(k6_partfun1(sK1),sK3)),
% 1.93/0.63    inference(backward_demodulation,[],[f219,f1873])).
% 1.93/0.63  fof(f1873,plain,(
% 1.93/0.63    sK1 = k1_relat_1(sK3)),
% 1.93/0.63    inference(resolution,[],[f1620,f243])).
% 1.93/0.63  fof(f243,plain,(
% 1.93/0.63    ~r1_tarski(sK1,k1_relat_1(sK3)) | sK1 = k1_relat_1(sK3)),
% 1.93/0.63    inference(resolution,[],[f221,f87])).
% 1.93/0.63  fof(f87,plain,(
% 1.93/0.63    ( ! [X0,X1] : (~r1_tarski(X0,X1) | ~r1_tarski(X1,X0) | X0 = X1) )),
% 1.93/0.63    inference(cnf_transformation,[],[f1])).
% 1.93/0.63  fof(f1,axiom,(
% 1.93/0.63    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 1.93/0.63  fof(f221,plain,(
% 1.93/0.63    r1_tarski(k1_relat_1(sK3),sK1)),
% 1.93/0.63    inference(subsumption_resolution,[],[f220,f182])).
% 1.93/0.63  fof(f182,plain,(
% 1.93/0.63    v1_relat_1(sK3)),
% 1.93/0.63    inference(resolution,[],[f54,f88])).
% 1.93/0.63  fof(f54,plain,(
% 1.93/0.63    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.93/0.63    inference(cnf_transformation,[],[f25])).
% 1.93/0.63  fof(f220,plain,(
% 1.93/0.63    ~v1_relat_1(sK3) | r1_tarski(k1_relat_1(sK3),sK1)),
% 1.93/0.63    inference(resolution,[],[f183,f84])).
% 1.93/0.63  fof(f84,plain,(
% 1.93/0.63    ( ! [X0,X1] : (~v1_relat_1(X1) | r1_tarski(k1_relat_1(X1),X0) | ~v4_relat_1(X1,X0)) )),
% 1.93/0.63    inference(cnf_transformation,[],[f41])).
% 1.93/0.63  fof(f41,plain,(
% 1.93/0.63    ! [X0,X1] : ((v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 1.93/0.63    inference(ennf_transformation,[],[f2])).
% 1.93/0.63  fof(f2,axiom,(
% 1.93/0.63    ! [X0,X1] : (v1_relat_1(X1) => (v4_relat_1(X1,X0) <=> r1_tarski(k1_relat_1(X1),X0)))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d18_relat_1)).
% 1.93/0.63  fof(f183,plain,(
% 1.93/0.63    v4_relat_1(sK3,sK1)),
% 1.93/0.63    inference(resolution,[],[f54,f89])).
% 1.93/0.63  fof(f89,plain,(
% 1.93/0.63    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.93/0.63    inference(cnf_transformation,[],[f43])).
% 1.93/0.63  fof(f43,plain,(
% 1.93/0.63    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.93/0.63    inference(ennf_transformation,[],[f15])).
% 1.93/0.63  fof(f15,axiom,(
% 1.93/0.63    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.93/0.63  fof(f1620,plain,(
% 1.93/0.63    r1_tarski(sK1,k1_relat_1(sK3))),
% 1.93/0.63    inference(subsumption_resolution,[],[f1578,f99])).
% 1.93/0.63  fof(f99,plain,(
% 1.93/0.63    ( ! [X0] : (k1_relat_1(k6_partfun1(X0)) = X0) )),
% 1.93/0.63    inference(definition_unfolding,[],[f67,f64])).
% 1.93/0.63  fof(f64,plain,(
% 1.93/0.63    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.93/0.63    inference(cnf_transformation,[],[f20])).
% 1.93/0.63  fof(f20,axiom,(
% 1.93/0.63    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.93/0.63  fof(f67,plain,(
% 1.93/0.63    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 1.93/0.63    inference(cnf_transformation,[],[f6])).
% 1.93/0.63  fof(f6,axiom,(
% 1.93/0.63    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 1.93/0.63  fof(f1578,plain,(
% 1.93/0.63    sK0 != k1_relat_1(k6_partfun1(sK0)) | r1_tarski(sK1,k1_relat_1(sK3))),
% 1.93/0.63    inference(backward_demodulation,[],[f490,f1555])).
% 1.93/0.63  fof(f1555,plain,(
% 1.93/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.93/0.63    inference(resolution,[],[f1554,f1042])).
% 1.93/0.63  fof(f1042,plain,(
% 1.93/0.63    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 1.93/0.63    inference(forward_demodulation,[],[f1033,f1031])).
% 1.93/0.63  fof(f1031,plain,(
% 1.93/0.63    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.93/0.63    inference(subsumption_resolution,[],[f1026,f61])).
% 1.93/0.63  fof(f1026,plain,(
% 1.93/0.63    ~v1_funct_1(sK2) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 1.93/0.63    inference(resolution,[],[f197,f63])).
% 1.93/0.63  fof(f197,plain,(
% 1.93/0.63    ( ! [X6,X7,X5] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_1(X5) | k1_partfun1(X6,X7,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)) )),
% 1.93/0.63    inference(subsumption_resolution,[],[f190,f52])).
% 1.93/0.63  fof(f52,plain,(
% 1.93/0.63    v1_funct_1(sK3)),
% 1.93/0.63    inference(cnf_transformation,[],[f25])).
% 1.93/0.63  fof(f190,plain,(
% 1.93/0.63    ( ! [X6,X7,X5] : (~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_1(sK3) | k1_partfun1(X6,X7,sK1,sK0,X5,sK3) = k5_relat_1(X5,sK3)) )),
% 1.93/0.63    inference(resolution,[],[f54,f95])).
% 1.93/0.63  fof(f95,plain,(
% 1.93/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 1.93/0.63    inference(cnf_transformation,[],[f49])).
% 1.93/0.63  fof(f49,plain,(
% 1.93/0.63    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.93/0.63    inference(flattening,[],[f48])).
% 1.93/0.63  fof(f48,plain,(
% 1.93/0.63    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.93/0.63    inference(ennf_transformation,[],[f19])).
% 1.93/0.63  fof(f19,axiom,(
% 1.93/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 1.93/0.63  fof(f1033,plain,(
% 1.93/0.63    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.93/0.63    inference(backward_demodulation,[],[f268,f1031])).
% 1.93/0.63  fof(f268,plain,(
% 1.93/0.63    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.93/0.63    inference(subsumption_resolution,[],[f266,f66])).
% 1.93/0.63  fof(f66,plain,(
% 1.93/0.63    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 1.93/0.63    inference(cnf_transformation,[],[f18])).
% 1.93/0.63  fof(f18,axiom,(
% 1.93/0.63    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 1.93/0.63  fof(f266,plain,(
% 1.93/0.63    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 1.93/0.63    inference(resolution,[],[f56,f94])).
% 1.93/0.63  fof(f94,plain,(
% 1.93/0.63    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 1.93/0.63    inference(cnf_transformation,[],[f47])).
% 1.93/0.63  fof(f47,plain,(
% 1.93/0.63    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.93/0.63    inference(flattening,[],[f46])).
% 1.93/0.63  fof(f46,plain,(
% 1.93/0.63    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 1.93/0.63    inference(ennf_transformation,[],[f16])).
% 1.93/0.63  fof(f16,axiom,(
% 1.93/0.63    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 1.93/0.63  fof(f56,plain,(
% 1.93/0.63    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.93/0.63    inference(cnf_transformation,[],[f25])).
% 1.93/0.63  fof(f1554,plain,(
% 1.93/0.63    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 1.93/0.63    inference(subsumption_resolution,[],[f1553,f54])).
% 1.93/0.63  fof(f1553,plain,(
% 1.93/0.63    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.93/0.63    inference(subsumption_resolution,[],[f1552,f52])).
% 1.93/0.63  fof(f1552,plain,(
% 1.93/0.63    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.93/0.63    inference(subsumption_resolution,[],[f1551,f63])).
% 1.93/0.63  fof(f1551,plain,(
% 1.93/0.63    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.93/0.63    inference(subsumption_resolution,[],[f1550,f61])).
% 1.93/0.63  fof(f1550,plain,(
% 1.93/0.63    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.93/0.63    inference(superposition,[],[f97,f1031])).
% 1.93/0.63  fof(f97,plain,(
% 1.93/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))) )),
% 1.93/0.63    inference(cnf_transformation,[],[f51])).
% 1.93/0.63  fof(f51,plain,(
% 1.93/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 1.93/0.63    inference(flattening,[],[f50])).
% 1.93/0.63  fof(f50,plain,(
% 1.93/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 1.93/0.63    inference(ennf_transformation,[],[f17])).
% 1.93/0.63  fof(f17,axiom,(
% 1.93/0.63    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 1.93/0.63  fof(f490,plain,(
% 1.93/0.63    sK0 != k1_relat_1(k5_relat_1(sK2,sK3)) | r1_tarski(sK1,k1_relat_1(sK3))),
% 1.93/0.63    inference(subsumption_resolution,[],[f482,f182])).
% 1.93/0.63  fof(f482,plain,(
% 1.93/0.63    sK0 != k1_relat_1(k5_relat_1(sK2,sK3)) | ~v1_relat_1(sK3) | r1_tarski(sK1,k1_relat_1(sK3))),
% 1.93/0.63    inference(resolution,[],[f333,f52])).
% 1.93/0.63  fof(f333,plain,(
% 1.93/0.63    ( ! [X1] : (~v1_funct_1(X1) | sK0 != k1_relat_1(k5_relat_1(sK2,X1)) | ~v1_relat_1(X1) | r1_tarski(sK1,k1_relat_1(X1))) )),
% 1.93/0.63    inference(backward_demodulation,[],[f322,f331])).
% 1.93/0.63  fof(f331,plain,(
% 1.93/0.63    sK1 = k2_relat_1(sK2)),
% 1.93/0.63    inference(resolution,[],[f179,f248])).
% 1.93/0.63  fof(f179,plain,(
% 1.93/0.63    ~v1_relat_1(sK2) | sK1 = k2_relat_1(sK2)),
% 1.93/0.63    inference(forward_demodulation,[],[f177,f98])).
% 1.93/0.63  fof(f98,plain,(
% 1.93/0.63    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 1.93/0.63    inference(definition_unfolding,[],[f68,f64])).
% 1.93/0.63  fof(f68,plain,(
% 1.93/0.63    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 1.93/0.63    inference(cnf_transformation,[],[f6])).
% 1.93/0.63  fof(f177,plain,(
% 1.93/0.63    k2_relat_1(sK2) = k2_relat_1(k6_partfun1(sK1)) | ~v1_relat_1(sK2)),
% 1.93/0.63    inference(backward_demodulation,[],[f132,f176])).
% 1.93/0.63  fof(f176,plain,(
% 1.93/0.63    k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 1.93/0.63    inference(subsumption_resolution,[],[f175,f59])).
% 1.93/0.63  fof(f59,plain,(
% 1.93/0.63    k1_xboole_0 != sK1),
% 1.93/0.63    inference(cnf_transformation,[],[f25])).
% 1.93/0.63  fof(f175,plain,(
% 1.93/0.63    k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 1.93/0.63    inference(subsumption_resolution,[],[f174,f57])).
% 1.93/0.63  fof(f174,plain,(
% 1.93/0.63    ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 1.93/0.63    inference(subsumption_resolution,[],[f173,f55])).
% 1.93/0.63  fof(f55,plain,(
% 1.93/0.63    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.93/0.63    inference(cnf_transformation,[],[f25])).
% 1.93/0.63  fof(f173,plain,(
% 1.93/0.63    sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 1.93/0.63    inference(subsumption_resolution,[],[f172,f63])).
% 1.93/0.63  fof(f172,plain,(
% 1.93/0.63    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 1.93/0.63    inference(subsumption_resolution,[],[f162,f61])).
% 1.93/0.63  fof(f162,plain,(
% 1.93/0.63    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k5_relat_1(k2_funct_1(sK2),sK2) = k6_partfun1(sK1)),
% 1.93/0.63    inference(resolution,[],[f62,f92])).
% 1.93/0.63  fof(f92,plain,(
% 1.93/0.63    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)) )),
% 1.93/0.63    inference(cnf_transformation,[],[f45])).
% 1.93/0.63  fof(f45,plain,(
% 1.93/0.63    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.93/0.63    inference(flattening,[],[f44])).
% 1.93/0.63  fof(f44,plain,(
% 1.93/0.63    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.93/0.63    inference(ennf_transformation,[],[f21])).
% 1.93/0.63  fof(f21,axiom,(
% 1.93/0.63    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 1.93/0.63  fof(f62,plain,(
% 1.93/0.63    v1_funct_2(sK2,sK0,sK1)),
% 1.93/0.63    inference(cnf_transformation,[],[f25])).
% 1.93/0.63  fof(f132,plain,(
% 1.93/0.63    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2))),
% 1.93/0.63    inference(subsumption_resolution,[],[f125,f61])).
% 1.93/0.63  fof(f125,plain,(
% 1.93/0.63    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k2_relat_1(sK2) = k2_relat_1(k5_relat_1(k2_funct_1(sK2),sK2))),
% 1.93/0.63    inference(resolution,[],[f57,f79])).
% 1.93/0.63  fof(f79,plain,(
% 1.93/0.63    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0))) )),
% 1.93/0.63    inference(cnf_transformation,[],[f36])).
% 1.93/0.63  fof(f36,plain,(
% 1.93/0.63    ! [X0] : ((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.93/0.63    inference(flattening,[],[f35])).
% 1.93/0.63  fof(f35,plain,(
% 1.93/0.63    ! [X0] : (((k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.93/0.63    inference(ennf_transformation,[],[f13])).
% 1.93/0.63  fof(f13,axiom,(
% 1.93/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k2_relat_1(X0) = k2_relat_1(k5_relat_1(k2_funct_1(X0),X0)) & k2_relat_1(X0) = k1_relat_1(k5_relat_1(k2_funct_1(X0),X0)))))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_funct_1)).
% 1.93/0.63  fof(f322,plain,(
% 1.93/0.63    ( ! [X1] : (sK0 != k1_relat_1(k5_relat_1(sK2,X1)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | r1_tarski(k2_relat_1(sK2),k1_relat_1(X1))) )),
% 1.93/0.63    inference(subsumption_resolution,[],[f317,f248])).
% 1.93/0.63  fof(f317,plain,(
% 1.93/0.63    ( ! [X1] : (sK0 != k1_relat_1(k5_relat_1(sK2,X1)) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(sK2) | r1_tarski(k2_relat_1(sK2),k1_relat_1(X1))) )),
% 1.93/0.63    inference(backward_demodulation,[],[f143,f314])).
% 1.93/0.63  fof(f314,plain,(
% 1.93/0.63    sK0 = k1_relat_1(sK2)),
% 1.93/0.63    inference(resolution,[],[f170,f248])).
% 1.93/0.63  fof(f170,plain,(
% 1.93/0.63    ~v1_relat_1(sK2) | sK0 = k1_relat_1(sK2)),
% 1.93/0.63    inference(forward_demodulation,[],[f168,f98])).
% 1.93/0.63  fof(f168,plain,(
% 1.93/0.63    k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0)) | ~v1_relat_1(sK2)),
% 1.93/0.63    inference(backward_demodulation,[],[f134,f167])).
% 1.93/0.63  fof(f167,plain,(
% 1.93/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.93/0.63    inference(subsumption_resolution,[],[f166,f59])).
% 1.93/0.63  fof(f166,plain,(
% 1.93/0.63    k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.93/0.63    inference(subsumption_resolution,[],[f165,f57])).
% 1.93/0.63  fof(f165,plain,(
% 1.93/0.63    ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.93/0.63    inference(subsumption_resolution,[],[f164,f55])).
% 1.93/0.63  fof(f164,plain,(
% 1.93/0.63    sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.93/0.63    inference(subsumption_resolution,[],[f163,f63])).
% 1.93/0.63  fof(f163,plain,(
% 1.93/0.63    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.93/0.63    inference(subsumption_resolution,[],[f161,f61])).
% 1.93/0.63  fof(f161,plain,(
% 1.93/0.63    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.93/0.63    inference(resolution,[],[f62,f91])).
% 1.93/0.63  fof(f91,plain,(
% 1.93/0.63    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 1.93/0.63    inference(cnf_transformation,[],[f45])).
% 1.93/0.63  fof(f134,plain,(
% 1.93/0.63    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))),
% 1.93/0.63    inference(subsumption_resolution,[],[f127,f61])).
% 1.93/0.63  fof(f127,plain,(
% 1.93/0.63    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k5_relat_1(sK2,k2_funct_1(sK2)))),
% 1.93/0.63    inference(resolution,[],[f57,f81])).
% 1.93/0.63  fof(f81,plain,(
% 1.93/0.63    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) )),
% 1.93/0.63    inference(cnf_transformation,[],[f38])).
% 1.93/0.63  fof(f38,plain,(
% 1.93/0.63    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.93/0.63    inference(flattening,[],[f37])).
% 1.93/0.63  fof(f37,plain,(
% 1.93/0.63    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0)))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.93/0.63    inference(ennf_transformation,[],[f12])).
% 1.93/0.63  fof(f12,axiom,(
% 1.93/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k5_relat_1(X0,k2_funct_1(X0))) & k1_relat_1(X0) = k1_relat_1(k5_relat_1(X0,k2_funct_1(X0))))))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_funct_1)).
% 1.93/0.63  fof(f143,plain,(
% 1.93/0.63    ( ! [X1] : (~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(sK2) | k1_relat_1(sK2) != k1_relat_1(k5_relat_1(sK2,X1)) | r1_tarski(k2_relat_1(sK2),k1_relat_1(X1))) )),
% 1.93/0.63    inference(resolution,[],[f61,f82])).
% 1.93/0.63  fof(f82,plain,(
% 1.93/0.63    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | r1_tarski(k2_relat_1(X1),k1_relat_1(X0))) )),
% 1.93/0.63    inference(cnf_transformation,[],[f40])).
% 1.93/0.63  fof(f40,plain,(
% 1.93/0.63    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.93/0.63    inference(flattening,[],[f39])).
% 1.93/0.63  fof(f39,plain,(
% 1.93/0.63    ! [X0] : (! [X1] : ((r1_tarski(k2_relat_1(X1),k1_relat_1(X0)) | k1_relat_1(X1) != k1_relat_1(k5_relat_1(X1,X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.93/0.63    inference(ennf_transformation,[],[f11])).
% 1.93/0.63  fof(f11,axiom,(
% 1.93/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (k1_relat_1(X1) = k1_relat_1(k5_relat_1(X1,X0)) => r1_tarski(k2_relat_1(X1),k1_relat_1(X0)))))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t27_funct_1)).
% 1.93/0.63  fof(f219,plain,(
% 1.93/0.63    sK3 = k5_relat_1(k6_partfun1(k1_relat_1(sK3)),sK3)),
% 1.93/0.63    inference(resolution,[],[f182,f101])).
% 1.93/0.63  fof(f101,plain,(
% 1.93/0.63    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0) )),
% 1.93/0.63    inference(definition_unfolding,[],[f71,f64])).
% 1.93/0.63  fof(f71,plain,(
% 1.93/0.63    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 1.93/0.63    inference(cnf_transformation,[],[f28])).
% 1.93/0.63  fof(f28,plain,(
% 1.93/0.63    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 1.93/0.63    inference(ennf_transformation,[],[f7])).
% 1.93/0.63  fof(f7,axiom,(
% 1.93/0.63    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 1.93/0.63  fof(f2534,plain,(
% 1.93/0.63    k5_relat_1(sK3,k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)),
% 1.93/0.63    inference(backward_demodulation,[],[f1579,f2476])).
% 1.93/0.63  fof(f2476,plain,(
% 1.93/0.63    k6_partfun1(sK1) = k5_relat_1(sK3,sK2)),
% 1.93/0.63    inference(forward_demodulation,[],[f2475,f358])).
% 1.93/0.63  fof(f358,plain,(
% 1.93/0.63    k6_partfun1(sK1) = k5_relat_1(k4_relat_1(sK2),sK2)),
% 1.93/0.63    inference(backward_demodulation,[],[f176,f354])).
% 1.93/0.63  fof(f2475,plain,(
% 1.93/0.63    k5_relat_1(k4_relat_1(sK2),sK2) = k5_relat_1(sK3,sK2)),
% 1.93/0.63    inference(forward_demodulation,[],[f2474,f2409])).
% 1.93/0.63  fof(f2409,plain,(
% 1.93/0.63    k5_relat_1(sK3,sK2) = k5_relat_1(k6_partfun1(sK1),k5_relat_1(sK3,sK2))),
% 1.93/0.63    inference(backward_demodulation,[],[f1257,f2404])).
% 1.93/0.63  fof(f2404,plain,(
% 1.93/0.63    sK1 = k1_relat_1(k5_relat_1(sK3,sK2))),
% 1.93/0.63    inference(resolution,[],[f1540,f1635])).
% 1.93/0.63  fof(f1635,plain,(
% 1.93/0.63    r1_tarski(sK1,k1_relat_1(k5_relat_1(sK3,sK2)))),
% 1.93/0.63    inference(subsumption_resolution,[],[f1634,f1205])).
% 1.93/0.63  fof(f1205,plain,(
% 1.93/0.63    v1_relat_1(k5_relat_1(sK3,sK2))),
% 1.93/0.63    inference(resolution,[],[f1204,f88])).
% 1.93/0.63  fof(f1204,plain,(
% 1.93/0.63    m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1)))),
% 1.93/0.63    inference(subsumption_resolution,[],[f1203,f63])).
% 1.93/0.63  fof(f1203,plain,(
% 1.93/0.63    m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.93/0.63    inference(subsumption_resolution,[],[f1202,f61])).
% 1.93/0.63  fof(f1202,plain,(
% 1.93/0.63    m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.93/0.63    inference(subsumption_resolution,[],[f1201,f54])).
% 1.93/0.63  fof(f1201,plain,(
% 1.93/0.63    m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.93/0.63    inference(subsumption_resolution,[],[f1200,f52])).
% 1.93/0.63  fof(f1200,plain,(
% 1.93/0.63    m1_subset_1(k5_relat_1(sK3,sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.93/0.63    inference(superposition,[],[f97,f878])).
% 1.93/0.63  fof(f878,plain,(
% 1.93/0.63    k5_relat_1(sK3,sK2) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)),
% 1.93/0.63    inference(subsumption_resolution,[],[f852,f61])).
% 1.93/0.63  fof(f852,plain,(
% 1.93/0.63    ~v1_funct_1(sK2) | k5_relat_1(sK3,sK2) = k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)),
% 1.93/0.63    inference(resolution,[],[f196,f63])).
% 1.93/0.63  fof(f196,plain,(
% 1.93/0.63    ( ! [X4,X2,X3] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_1(X2) | k1_partfun1(sK1,sK0,X3,X4,sK3,X2) = k5_relat_1(sK3,X2)) )),
% 1.93/0.63    inference(subsumption_resolution,[],[f189,f52])).
% 1.93/0.63  fof(f189,plain,(
% 1.93/0.63    ( ! [X4,X2,X3] : (~v1_funct_1(sK3) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_partfun1(sK1,sK0,X3,X4,sK3,X2) = k5_relat_1(sK3,X2)) )),
% 1.93/0.63    inference(resolution,[],[f54,f95])).
% 1.93/0.63  fof(f1634,plain,(
% 1.93/0.63    r1_tarski(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) | ~v1_relat_1(k5_relat_1(sK3,sK2))),
% 1.93/0.63    inference(subsumption_resolution,[],[f1622,f314])).
% 1.93/0.63  fof(f1622,plain,(
% 1.93/0.63    sK0 != k1_relat_1(sK2) | r1_tarski(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) | ~v1_relat_1(k5_relat_1(sK3,sK2))),
% 1.93/0.63    inference(backward_demodulation,[],[f896,f1621])).
% 1.93/0.63  fof(f1621,plain,(
% 1.93/0.63    sK2 = k5_relat_1(sK2,k5_relat_1(sK3,sK2))),
% 1.93/0.63    inference(forward_demodulation,[],[f1585,f319])).
% 1.93/0.63  fof(f319,plain,(
% 1.93/0.63    sK2 = k5_relat_1(k6_partfun1(sK0),sK2)),
% 1.93/0.63    inference(backward_demodulation,[],[f288,f314])).
% 1.93/0.63  fof(f288,plain,(
% 1.93/0.63    sK2 = k5_relat_1(k6_partfun1(k1_relat_1(sK2)),sK2)),
% 1.93/0.63    inference(resolution,[],[f248,f101])).
% 1.93/0.63  fof(f1585,plain,(
% 1.93/0.63    k5_relat_1(k6_partfun1(sK0),sK2) = k5_relat_1(sK2,k5_relat_1(sK3,sK2))),
% 1.93/0.63    inference(backward_demodulation,[],[f695,f1555])).
% 1.93/0.63  fof(f695,plain,(
% 1.93/0.63    k5_relat_1(k5_relat_1(sK2,sK3),sK2) = k5_relat_1(sK2,k5_relat_1(sK3,sK2))),
% 1.93/0.63    inference(resolution,[],[f659,f248])).
% 1.93/0.63  fof(f659,plain,(
% 1.93/0.63    ( ! [X11] : (~v1_relat_1(X11) | k5_relat_1(k5_relat_1(sK2,sK3),X11) = k5_relat_1(sK2,k5_relat_1(sK3,X11))) )),
% 1.93/0.63    inference(resolution,[],[f205,f248])).
% 1.93/0.63  fof(f205,plain,(
% 1.93/0.63    ( ! [X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | k5_relat_1(k5_relat_1(X2,sK3),X3) = k5_relat_1(X2,k5_relat_1(sK3,X3))) )),
% 1.93/0.63    inference(resolution,[],[f182,f74])).
% 1.93/0.63  fof(f74,plain,(
% 1.93/0.63    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 1.93/0.63    inference(cnf_transformation,[],[f30])).
% 1.93/0.63  fof(f30,plain,(
% 1.93/0.63    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 1.93/0.63    inference(ennf_transformation,[],[f5])).
% 1.93/0.63  fof(f5,axiom,(
% 1.93/0.63    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 1.93/0.63  fof(f896,plain,(
% 1.93/0.63    r1_tarski(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) | sK0 != k1_relat_1(k5_relat_1(sK2,k5_relat_1(sK3,sK2))) | ~v1_relat_1(k5_relat_1(sK3,sK2))),
% 1.93/0.63    inference(forward_demodulation,[],[f895,f878])).
% 1.93/0.63  fof(f895,plain,(
% 1.93/0.63    sK0 != k1_relat_1(k5_relat_1(sK2,k5_relat_1(sK3,sK2))) | ~v1_relat_1(k5_relat_1(sK3,sK2)) | r1_tarski(sK1,k1_relat_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)))),
% 1.93/0.63    inference(forward_demodulation,[],[f884,f878])).
% 1.93/0.63  fof(f884,plain,(
% 1.93/0.63    ~v1_relat_1(k5_relat_1(sK3,sK2)) | sK0 != k1_relat_1(k5_relat_1(sK2,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2))) | r1_tarski(sK1,k1_relat_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)))),
% 1.93/0.63    inference(backward_demodulation,[],[f595,f878])).
% 1.93/0.63  fof(f595,plain,(
% 1.93/0.63    sK0 != k1_relat_1(k5_relat_1(sK2,k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2))) | ~v1_relat_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)) | r1_tarski(sK1,k1_relat_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2)))),
% 1.93/0.63    inference(resolution,[],[f556,f333])).
% 1.93/0.63  fof(f556,plain,(
% 1.93/0.63    v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2))),
% 1.93/0.63    inference(subsumption_resolution,[],[f553,f61])).
% 1.93/0.63  fof(f553,plain,(
% 1.93/0.63    ~v1_funct_1(sK2) | v1_funct_1(k1_partfun1(sK1,sK0,sK0,sK1,sK3,sK2))),
% 1.93/0.63    inference(resolution,[],[f198,f63])).
% 1.93/0.63  fof(f198,plain,(
% 1.93/0.63    ( ! [X10,X8,X9] : (~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | ~v1_funct_1(X8) | v1_funct_1(k1_partfun1(sK1,sK0,X9,X10,sK3,X8))) )),
% 1.93/0.63    inference(subsumption_resolution,[],[f191,f52])).
% 1.93/0.63  fof(f191,plain,(
% 1.93/0.63    ( ! [X10,X8,X9] : (~v1_funct_1(sK3) | ~v1_funct_1(X8) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(X9,X10))) | v1_funct_1(k1_partfun1(sK1,sK0,X9,X10,sK3,X8))) )),
% 1.93/0.63    inference(resolution,[],[f54,f96])).
% 1.93/0.63  fof(f96,plain,(
% 1.93/0.63    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) )),
% 1.93/0.63    inference(cnf_transformation,[],[f51])).
% 1.93/0.63  fof(f1540,plain,(
% 1.93/0.63    ~r1_tarski(sK1,k1_relat_1(k5_relat_1(sK3,sK2))) | sK1 = k1_relat_1(k5_relat_1(sK3,sK2))),
% 1.93/0.63    inference(resolution,[],[f1355,f87])).
% 1.93/0.63  fof(f1355,plain,(
% 1.93/0.63    r1_tarski(k1_relat_1(k5_relat_1(sK3,sK2)),sK1)),
% 1.93/0.63    inference(subsumption_resolution,[],[f1354,f1205])).
% 1.93/0.63  fof(f1354,plain,(
% 1.93/0.63    ~v1_relat_1(k5_relat_1(sK3,sK2)) | r1_tarski(k1_relat_1(k5_relat_1(sK3,sK2)),sK1)),
% 1.93/0.63    inference(resolution,[],[f1206,f84])).
% 1.93/0.63  fof(f1206,plain,(
% 1.93/0.63    v4_relat_1(k5_relat_1(sK3,sK2),sK1)),
% 1.93/0.63    inference(resolution,[],[f1204,f89])).
% 1.93/0.63  fof(f1257,plain,(
% 1.93/0.63    k5_relat_1(sK3,sK2) = k5_relat_1(k6_partfun1(k1_relat_1(k5_relat_1(sK3,sK2))),k5_relat_1(sK3,sK2))),
% 1.93/0.63    inference(resolution,[],[f1205,f101])).
% 1.93/0.63  fof(f2474,plain,(
% 1.93/0.63    k5_relat_1(k4_relat_1(sK2),sK2) = k5_relat_1(k6_partfun1(sK1),k5_relat_1(sK3,sK2))),
% 1.93/0.63    inference(forward_demodulation,[],[f2459,f1621])).
% 1.93/0.63  fof(f2459,plain,(
% 1.93/0.63    k5_relat_1(k6_partfun1(sK1),k5_relat_1(sK3,sK2)) = k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,k5_relat_1(sK3,sK2)))),
% 1.93/0.63    inference(resolution,[],[f848,f1205])).
% 1.93/0.63  fof(f848,plain,(
% 1.93/0.63    ( ! [X6] : (~v1_relat_1(X6) | k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,X6)) = k5_relat_1(k6_partfun1(sK1),X6)) )),
% 1.93/0.63    inference(forward_demodulation,[],[f842,f358])).
% 1.93/0.63  fof(f842,plain,(
% 1.93/0.63    ( ! [X6] : (~v1_relat_1(X6) | k5_relat_1(k5_relat_1(k4_relat_1(sK2),sK2),X6) = k5_relat_1(k4_relat_1(sK2),k5_relat_1(sK2,X6))) )),
% 1.93/0.63    inference(resolution,[],[f274,f359])).
% 1.93/0.63  fof(f359,plain,(
% 1.93/0.63    v1_relat_1(k4_relat_1(sK2))),
% 1.93/0.63    inference(backward_demodulation,[],[f269,f354])).
% 1.93/0.63  fof(f269,plain,(
% 1.93/0.63    v1_relat_1(k2_funct_1(sK2))),
% 1.93/0.63    inference(resolution,[],[f248,f135])).
% 1.93/0.63  fof(f135,plain,(
% 1.93/0.63    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2))),
% 1.93/0.63    inference(resolution,[],[f61,f75])).
% 1.93/0.63  fof(f75,plain,(
% 1.93/0.63    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 1.93/0.63    inference(cnf_transformation,[],[f32])).
% 1.93/0.63  fof(f32,plain,(
% 1.93/0.63    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.93/0.63    inference(flattening,[],[f31])).
% 1.93/0.63  fof(f31,plain,(
% 1.93/0.63    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.93/0.63    inference(ennf_transformation,[],[f10])).
% 1.93/0.63  fof(f10,axiom,(
% 1.93/0.63    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.93/0.63  fof(f274,plain,(
% 1.93/0.63    ( ! [X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | k5_relat_1(k5_relat_1(X2,sK2),X3) = k5_relat_1(X2,k5_relat_1(sK2,X3))) )),
% 1.93/0.63    inference(resolution,[],[f248,f74])).
% 1.93/0.63  fof(f1579,plain,(
% 1.93/0.63    k5_relat_1(k5_relat_1(sK3,sK2),sK3) = k5_relat_1(sK3,k6_partfun1(sK0))),
% 1.93/0.63    inference(backward_demodulation,[],[f546,f1555])).
% 1.93/0.63  fof(f546,plain,(
% 1.93/0.63    k5_relat_1(k5_relat_1(sK3,sK2),sK3) = k5_relat_1(sK3,k5_relat_1(sK2,sK3))),
% 1.93/0.63    inference(resolution,[],[f537,f182])).
% 1.93/0.63  fof(f537,plain,(
% 1.93/0.63    ( ! [X11] : (~v1_relat_1(X11) | k5_relat_1(k5_relat_1(sK3,sK2),X11) = k5_relat_1(sK3,k5_relat_1(sK2,X11))) )),
% 1.93/0.63    inference(resolution,[],[f204,f248])).
% 1.93/0.63  fof(f204,plain,(
% 1.93/0.63    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k5_relat_1(k5_relat_1(sK3,X0),X1) = k5_relat_1(sK3,k5_relat_1(X0,X1))) )),
% 1.93/0.63    inference(resolution,[],[f182,f74])).
% 1.93/0.63  fof(f2596,plain,(
% 1.93/0.63    k4_relat_1(sK2) = k5_relat_1(sK3,k6_partfun1(sK0))),
% 1.93/0.63    inference(forward_demodulation,[],[f2482,f370])).
% 1.93/0.63  fof(f370,plain,(
% 1.93/0.63    k4_relat_1(sK2) = k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2))),
% 1.93/0.63    inference(forward_demodulation,[],[f366,f335])).
% 1.93/0.63  fof(f335,plain,(
% 1.93/0.63    sK1 = k1_relat_1(k4_relat_1(sK2))),
% 1.93/0.63    inference(backward_demodulation,[],[f271,f331])).
% 1.93/0.63  fof(f271,plain,(
% 1.93/0.63    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))),
% 1.93/0.63    inference(resolution,[],[f248,f72])).
% 1.93/0.63  fof(f72,plain,(
% 1.93/0.63    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 1.93/0.63    inference(cnf_transformation,[],[f29])).
% 1.93/0.63  fof(f29,plain,(
% 1.93/0.63    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 1.93/0.63    inference(ennf_transformation,[],[f4])).
% 1.93/0.63  fof(f4,axiom,(
% 1.93/0.63    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 1.93/0.63    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 1.93/0.63  fof(f366,plain,(
% 1.93/0.63    k4_relat_1(sK2) = k5_relat_1(k6_partfun1(k1_relat_1(k4_relat_1(sK2))),k4_relat_1(sK2))),
% 1.93/0.63    inference(backward_demodulation,[],[f309,f354])).
% 1.93/0.63  fof(f309,plain,(
% 1.93/0.63    k2_funct_1(sK2) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK2))),k2_funct_1(sK2))),
% 1.93/0.63    inference(resolution,[],[f269,f101])).
% 1.93/0.63  fof(f2482,plain,(
% 1.93/0.63    k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2)) = k5_relat_1(sK3,k6_partfun1(sK0))),
% 1.93/0.63    inference(backward_demodulation,[],[f547,f2476])).
% 1.93/0.63  fof(f547,plain,(
% 1.93/0.63    k5_relat_1(k5_relat_1(sK3,sK2),k4_relat_1(sK2)) = k5_relat_1(sK3,k6_partfun1(sK0))),
% 1.93/0.63    inference(forward_demodulation,[],[f541,f357])).
% 1.93/0.63  fof(f357,plain,(
% 1.93/0.63    k6_partfun1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2))),
% 1.93/0.63    inference(backward_demodulation,[],[f167,f354])).
% 1.93/0.63  fof(f541,plain,(
% 1.93/0.63    k5_relat_1(k5_relat_1(sK3,sK2),k4_relat_1(sK2)) = k5_relat_1(sK3,k5_relat_1(sK2,k4_relat_1(sK2)))),
% 1.93/0.63    inference(resolution,[],[f537,f359])).
% 1.93/0.63  % SZS output end Proof for theBenchmark
% 1.93/0.63  % (13791)------------------------------
% 1.93/0.63  % (13791)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.93/0.63  % (13791)Termination reason: Refutation
% 1.93/0.63  
% 1.93/0.63  % (13791)Memory used [KB]: 3070
% 1.93/0.63  % (13791)Time elapsed: 0.173 s
% 1.93/0.63  % (13791)------------------------------
% 1.93/0.63  % (13791)------------------------------
% 1.93/0.63  % (13773)Success in time 0.266 s
%------------------------------------------------------------------------------
