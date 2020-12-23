%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:40 EST 2020

% Result     : Theorem 2.99s
% Output     : Refutation 2.99s
% Verified   : 
% Statistics : Number of formulae       :  183 (3573 expanded)
%              Number of leaves         :   19 ( 644 expanded)
%              Depth                    :   32
%              Number of atoms          :  559 (26778 expanded)
%              Number of equality atoms :  195 (8385 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2163,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2162,f355])).

fof(f355,plain,(
    sK3 != k4_relat_1(sK2) ),
    inference(superposition,[],[f56,f321])).

fof(f321,plain,(
    k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(resolution,[],[f119,f258])).

fof(f258,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f59,f74])).

fof(f74,plain,(
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

fof(f59,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

fof(f22,plain,(
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
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f119,plain,
    ( ~ v1_relat_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f118,f57])).

fof(f57,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f118,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(resolution,[],[f53,f72])).

fof(f72,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f53,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f56,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f2162,plain,(
    sK3 = k4_relat_1(sK2) ),
    inference(backward_demodulation,[],[f335,f2157])).

fof(f2157,plain,(
    sK3 = k7_relat_1(k4_relat_1(sK2),sK1) ),
    inference(superposition,[],[f1980,f334])).

fof(f334,plain,(
    ! [X6] : k7_relat_1(k4_relat_1(sK2),X6) = k5_relat_1(k6_partfun1(X6),k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f308,f321])).

fof(f308,plain,(
    ! [X6] : k7_relat_1(k2_funct_1(sK2),X6) = k5_relat_1(k6_partfun1(X6),k2_funct_1(sK2)) ),
    inference(resolution,[],[f282,f90])).

fof(f90,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) ) ),
    inference(definition_unfolding,[],[f73,f61])).

fof(f61,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f282,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f258,f120])).

fof(f120,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f57,f70])).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f1980,plain,(
    sK3 = k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f1821,f1877])).

fof(f1877,plain,(
    k6_partfun1(sK1) = k5_relat_1(sK3,sK2) ),
    inference(backward_demodulation,[],[f1817,f1847])).

fof(f1847,plain,(
    sK2 = k4_relat_1(sK3) ),
    inference(forward_demodulation,[],[f1815,f1846])).

fof(f1846,plain,(
    sK2 = k7_relat_1(k4_relat_1(sK3),sK0) ),
    inference(forward_demodulation,[],[f1843,f296])).

fof(f296,plain,(
    sK2 = k5_relat_1(sK2,k6_partfun1(sK1)) ),
    inference(forward_demodulation,[],[f293,f277])).

fof(f277,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f259,f51])).

fof(f51,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f259,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f59,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f293,plain,(
    sK2 = k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2))) ),
    inference(resolution,[],[f258,f89])).

fof(f89,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ) ),
    inference(definition_unfolding,[],[f66,f61])).

fof(f66,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f1843,plain,(
    k5_relat_1(sK2,k6_partfun1(sK1)) = k7_relat_1(k4_relat_1(sK3),sK0) ),
    inference(backward_demodulation,[],[f1511,f1817])).

fof(f1511,plain,(
    k5_relat_1(sK2,k5_relat_1(sK3,k4_relat_1(sK3))) = k7_relat_1(k4_relat_1(sK3),sK0) ),
    inference(backward_demodulation,[],[f1251,f1491])).

fof(f1491,plain,(
    k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f1490,f48])).

fof(f48,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f1490,plain,
    ( ~ v1_funct_1(sK3)
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f1489,f197])).

fof(f197,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f50,f74])).

fof(f50,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f1489,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(resolution,[],[f1484,f72])).

fof(f1484,plain,(
    v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1483,f88])).

fof(f88,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f60,f61])).

fof(f60,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).

fof(f1483,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3) ),
    inference(forward_demodulation,[],[f1482,f1236])).

fof(f1236,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(backward_demodulation,[],[f793,f1198])).

fof(f1198,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f1197,f799])).

fof(f799,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(forward_demodulation,[],[f796,f793])).

fof(f796,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(backward_demodulation,[],[f313,f793])).

fof(f313,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(subsumption_resolution,[],[f311,f63])).

fof(f63,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f311,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(resolution,[],[f52,f84])).

fof(f84,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f52,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f1197,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f1196,f50])).

fof(f1196,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1195,f48])).

fof(f1195,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1194,f59])).

fof(f1194,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1193,f57])).

fof(f1193,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f87,f793])).

fof(f87,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f793,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f787,f57])).

fof(f787,plain,
    ( ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f222,f59])).

fof(f222,plain,(
    ! [X12,X10,X11] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ v1_funct_1(X10)
      | k1_partfun1(X11,X12,sK1,sK0,X10,sK3) = k5_relat_1(X10,sK3) ) ),
    inference(subsumption_resolution,[],[f210,f48])).

fof(f210,plain,(
    ! [X12,X10,X11] :
      ( ~ v1_funct_1(X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ v1_funct_1(sK3)
      | k1_partfun1(X11,X12,sK1,sK0,X10,sK3) = k5_relat_1(X10,sK3) ) ),
    inference(resolution,[],[f50,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f1482,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1481,f54])).

fof(f54,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f23])).

fof(f1481,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1480,f50])).

fof(f1480,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1479,f48])).

fof(f1479,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK3) ),
    inference(resolution,[],[f195,f49])).

fof(f49,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f195,plain,(
    ! [X6,X7] :
      ( ~ v1_funct_2(X6,sK1,X7)
      | ~ v1_funct_1(X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6))
      | k1_xboole_0 = X7
      | v2_funct_1(X6) ) ),
    inference(subsumption_resolution,[],[f194,f51])).

fof(f194,plain,(
    ! [X6,X7] :
      ( ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,sK1,X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6))
      | sK1 != k2_relset_1(sK0,sK1,sK2)
      | k1_xboole_0 = X7
      | v2_funct_1(X6) ) ),
    inference(subsumption_resolution,[],[f193,f59])).

fof(f193,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,sK1,X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6))
      | sK1 != k2_relset_1(sK0,sK1,sK2)
      | k1_xboole_0 = X7
      | v2_funct_1(X6) ) ),
    inference(subsumption_resolution,[],[f176,f57])).

fof(f176,plain,(
    ! [X6,X7] :
      ( ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,sK1,X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6))
      | sK1 != k2_relset_1(sK0,sK1,sK2)
      | k1_xboole_0 = X7
      | v2_funct_1(X6) ) ),
    inference(resolution,[],[f58,f82])).

fof(f82,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X0,X1)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,X1,X2)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | k2_relset_1(X0,X1,X3) != X1
      | k1_xboole_0 = X2
      | v2_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( ! [X4] :
          ( ( v2_funct_1(X4)
            & v2_funct_1(X3) )
          | ( k1_xboole_0 != X1
            & k1_xboole_0 = X2 )
          | k2_relset_1(X0,X1,X3) != X1
          | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
          | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          | ~ v1_funct_2(X4,X1,X2)
          | ~ v1_funct_1(X4) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f58,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f1251,plain,(
    k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) = k7_relat_1(k2_funct_1(sK3),sK0) ),
    inference(forward_demodulation,[],[f1230,f249])).

fof(f249,plain,(
    ! [X6] : k7_relat_1(k2_funct_1(sK3),X6) = k5_relat_1(k6_partfun1(X6),k2_funct_1(sK3)) ),
    inference(resolution,[],[f225,f90])).

fof(f225,plain,(
    v1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f197,f95])).

fof(f95,plain,
    ( ~ v1_relat_1(sK3)
    | v1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f48,f70])).

fof(f1230,plain,(
    k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f619,f1198])).

fof(f619,plain,(
    k5_relat_1(k5_relat_1(sK2,sK3),k2_funct_1(sK3)) = k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) ),
    inference(resolution,[],[f613,f225])).

fof(f613,plain,(
    ! [X11] :
      ( ~ v1_relat_1(X11)
      | k5_relat_1(k5_relat_1(sK2,sK3),X11) = k5_relat_1(sK2,k5_relat_1(sK3,X11)) ) ),
    inference(resolution,[],[f231,f258])).

fof(f231,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(X2,sK3),X3) = k5_relat_1(X2,k5_relat_1(sK3,X3)) ) ),
    inference(resolution,[],[f197,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f1815,plain,(
    k4_relat_1(sK3) = k7_relat_1(k4_relat_1(sK3),sK0) ),
    inference(backward_demodulation,[],[f1516,f1807])).

fof(f1807,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f1806,f1238])).

fof(f1238,plain,(
    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f797,f1198])).

fof(f797,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f52,f793])).

fof(f1806,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | sK0 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f1805,f1236])).

fof(f1805,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f1804,f59])).

fof(f1804,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f1803,f57])).

fof(f1803,plain,
    ( ~ v1_funct_1(sK2)
    | sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(resolution,[],[f218,f58])).

fof(f218,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,sK0,sK1)
      | ~ v1_funct_1(X0)
      | sK0 = k2_relat_1(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0)) ) ),
    inference(backward_demodulation,[],[f156,f198])).

fof(f198,plain,(
    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f50,f75])).

fof(f156,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0))
      | sK0 = k2_relset_1(sK1,sK0,sK3) ) ),
    inference(subsumption_resolution,[],[f155,f50])).

fof(f155,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0))
      | sK0 = k2_relset_1(sK1,sK0,sK3) ) ),
    inference(subsumption_resolution,[],[f143,f48])).

fof(f143,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0))
      | sK0 = k2_relset_1(sK1,sK0,sK3) ) ),
    inference(resolution,[],[f49,f78])).

fof(f78,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( ! [X3] :
          ( k2_relset_1(X0,X1,X2) = X1
          | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
          | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          | ~ v1_funct_2(X3,X1,X0)
          | ~ v1_funct_1(X3) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ! [X3] :
          ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(X3,X1,X0)
            & v1_funct_1(X3) )
         => ( r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
           => k2_relset_1(X0,X1,X2) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f1516,plain,(
    k4_relat_1(sK3) = k7_relat_1(k4_relat_1(sK3),k2_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f1496,f228])).

fof(f228,plain,(
    k2_relat_1(sK3) = k1_relat_1(k4_relat_1(sK3)) ),
    inference(resolution,[],[f197,f67])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).

fof(f1496,plain,(
    k4_relat_1(sK3) = k7_relat_1(k4_relat_1(sK3),k1_relat_1(k4_relat_1(sK3))) ),
    inference(backward_demodulation,[],[f239,f1491])).

fof(f239,plain,(
    k2_funct_1(sK3) = k7_relat_1(k2_funct_1(sK3),k1_relat_1(k2_funct_1(sK3))) ),
    inference(resolution,[],[f225,f65])).

fof(f65,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f1817,plain,(
    k6_partfun1(sK1) = k5_relat_1(sK3,k4_relat_1(sK3)) ),
    inference(trivial_inequality_removal,[],[f1814])).

fof(f1814,plain,
    ( sK0 != sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k4_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f1515,f1807])).

fof(f1515,plain,
    ( sK0 != k2_relat_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k4_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f1494,f1484])).

fof(f1494,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k4_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | sK0 != k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f220,f1491])).

fof(f220,plain,
    ( ~ v2_funct_1(sK3)
    | sK0 != k2_relat_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f151,f198])).

fof(f151,plain,
    ( sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f150,f54])).

fof(f150,plain,
    ( sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f149,f50])).

fof(f149,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f141,f48])).

fof(f141,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(resolution,[],[f49,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f1821,plain,(
    sK3 = k5_relat_1(k5_relat_1(sK3,sK2),k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f473,f1812])).

fof(f1812,plain,(
    sK3 = k5_relat_1(sK3,k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f236,f1807])).

fof(f236,plain,(
    sK3 = k5_relat_1(sK3,k6_partfun1(k2_relat_1(sK3))) ),
    inference(resolution,[],[f197,f89])).

fof(f473,plain,(
    k5_relat_1(k5_relat_1(sK3,sK2),k4_relat_1(sK2)) = k5_relat_1(sK3,k6_partfun1(sK0)) ),
    inference(forward_demodulation,[],[f467,f324])).

fof(f324,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f182,f321])).

fof(f182,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f181,f55])).

fof(f55,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f181,plain,
    ( k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f180,f53])).

fof(f180,plain,
    ( ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f179,f51])).

fof(f179,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f178,f59])).

fof(f178,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f170,f57])).

fof(f170,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(resolution,[],[f58,f76])).

fof(f467,plain,(
    k5_relat_1(k5_relat_1(sK3,sK2),k4_relat_1(sK2)) = k5_relat_1(sK3,k5_relat_1(sK2,k4_relat_1(sK2))) ),
    inference(resolution,[],[f463,f326])).

fof(f326,plain,(
    v1_relat_1(k4_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f282,f321])).

fof(f463,plain,(
    ! [X11] :
      ( ~ v1_relat_1(X11)
      | k5_relat_1(k5_relat_1(sK3,sK2),X11) = k5_relat_1(sK3,k5_relat_1(sK2,X11)) ) ),
    inference(resolution,[],[f230,f258])).

fof(f230,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | k5_relat_1(k5_relat_1(sK3,X0),X1) = k5_relat_1(sK3,k5_relat_1(X0,X1)) ) ),
    inference(resolution,[],[f197,f69])).

fof(f335,plain,(
    k4_relat_1(sK2) = k7_relat_1(k4_relat_1(sK2),sK1) ),
    inference(forward_demodulation,[],[f327,f295])).

fof(f295,plain,(
    sK1 = k1_relat_1(k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f285,f277])).

fof(f285,plain,(
    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) ),
    inference(resolution,[],[f258,f67])).

fof(f327,plain,(
    k4_relat_1(sK2) = k7_relat_1(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2))) ),
    inference(backward_demodulation,[],[f298,f321])).

fof(f298,plain,(
    k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2))) ),
    inference(resolution,[],[f282,f65])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n004.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 13:38:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.53  % (10351)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (10355)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.56  % (10367)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.57  % (10359)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.57  % (10347)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.57  % (10345)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.57  % (10350)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.59  % (10363)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.60  % (10348)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.60  % (10349)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.60  % (10354)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.60  % (10369)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.61  % (10368)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.61  % (10374)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.61  % (10364)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.61  % (10365)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.61  % (10360)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.61  % (10370)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.62  % (10366)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.84/0.62  % (10346)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 1.84/0.62  % (10353)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 1.84/0.62  % (10372)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 1.84/0.62  % (10373)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 1.84/0.62  % (10352)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 1.84/0.63  % (10361)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.84/0.64  % (10356)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 1.84/0.64  % (10361)Refutation not found, incomplete strategy% (10361)------------------------------
% 1.84/0.64  % (10361)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.84/0.64  % (10361)Termination reason: Refutation not found, incomplete strategy
% 1.84/0.64  
% 1.84/0.64  % (10361)Memory used [KB]: 10746
% 1.84/0.64  % (10361)Time elapsed: 0.157 s
% 1.84/0.64  % (10361)------------------------------
% 1.84/0.64  % (10361)------------------------------
% 1.84/0.64  % (10357)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 2.14/0.64  % (10358)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 2.23/0.66  % (10371)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 2.23/0.66  % (10362)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 2.99/0.77  % (10362)Refutation found. Thanks to Tanya!
% 2.99/0.77  % SZS status Theorem for theBenchmark
% 2.99/0.77  % SZS output start Proof for theBenchmark
% 2.99/0.77  fof(f2163,plain,(
% 2.99/0.77    $false),
% 2.99/0.77    inference(subsumption_resolution,[],[f2162,f355])).
% 2.99/0.77  fof(f355,plain,(
% 2.99/0.77    sK3 != k4_relat_1(sK2)),
% 2.99/0.77    inference(superposition,[],[f56,f321])).
% 2.99/0.77  fof(f321,plain,(
% 2.99/0.77    k2_funct_1(sK2) = k4_relat_1(sK2)),
% 2.99/0.77    inference(resolution,[],[f119,f258])).
% 2.99/0.77  fof(f258,plain,(
% 2.99/0.77    v1_relat_1(sK2)),
% 2.99/0.77    inference(resolution,[],[f59,f74])).
% 2.99/0.77  fof(f74,plain,(
% 2.99/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.99/0.77    inference(cnf_transformation,[],[f34])).
% 2.99/0.77  fof(f34,plain,(
% 2.99/0.77    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.99/0.77    inference(ennf_transformation,[],[f10])).
% 2.99/0.77  fof(f10,axiom,(
% 2.99/0.77    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.99/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.99/0.77  fof(f59,plain,(
% 2.99/0.77    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.99/0.77    inference(cnf_transformation,[],[f23])).
% 2.99/0.77  fof(f23,plain,(
% 2.99/0.77    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.99/0.77    inference(flattening,[],[f22])).
% 2.99/0.77  fof(f22,plain,(
% 2.99/0.77    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.99/0.77    inference(ennf_transformation,[],[f21])).
% 2.99/0.77  fof(f21,negated_conjecture,(
% 2.99/0.77    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.99/0.77    inference(negated_conjecture,[],[f20])).
% 2.99/0.77  fof(f20,conjecture,(
% 2.99/0.77    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.99/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 2.99/0.77  fof(f119,plain,(
% 2.99/0.77    ~v1_relat_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2)),
% 2.99/0.77    inference(subsumption_resolution,[],[f118,f57])).
% 2.99/0.77  fof(f57,plain,(
% 2.99/0.77    v1_funct_1(sK2)),
% 2.99/0.77    inference(cnf_transformation,[],[f23])).
% 2.99/0.77  fof(f118,plain,(
% 2.99/0.77    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | k2_funct_1(sK2) = k4_relat_1(sK2)),
% 2.99/0.77    inference(resolution,[],[f53,f72])).
% 2.99/0.77  fof(f72,plain,(
% 2.99/0.77    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 2.99/0.77    inference(cnf_transformation,[],[f32])).
% 2.99/0.77  fof(f32,plain,(
% 2.99/0.77    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.99/0.77    inference(flattening,[],[f31])).
% 2.99/0.77  fof(f31,plain,(
% 2.99/0.77    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.99/0.77    inference(ennf_transformation,[],[f7])).
% 2.99/0.77  fof(f7,axiom,(
% 2.99/0.77    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.99/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 2.99/0.77  fof(f53,plain,(
% 2.99/0.77    v2_funct_1(sK2)),
% 2.99/0.77    inference(cnf_transformation,[],[f23])).
% 2.99/0.77  fof(f56,plain,(
% 2.99/0.77    sK3 != k2_funct_1(sK2)),
% 2.99/0.77    inference(cnf_transformation,[],[f23])).
% 2.99/0.77  fof(f2162,plain,(
% 2.99/0.77    sK3 = k4_relat_1(sK2)),
% 2.99/0.77    inference(backward_demodulation,[],[f335,f2157])).
% 2.99/0.77  fof(f2157,plain,(
% 2.99/0.77    sK3 = k7_relat_1(k4_relat_1(sK2),sK1)),
% 2.99/0.77    inference(superposition,[],[f1980,f334])).
% 2.99/0.77  fof(f334,plain,(
% 2.99/0.77    ( ! [X6] : (k7_relat_1(k4_relat_1(sK2),X6) = k5_relat_1(k6_partfun1(X6),k4_relat_1(sK2))) )),
% 2.99/0.77    inference(backward_demodulation,[],[f308,f321])).
% 2.99/0.77  fof(f308,plain,(
% 2.99/0.77    ( ! [X6] : (k7_relat_1(k2_funct_1(sK2),X6) = k5_relat_1(k6_partfun1(X6),k2_funct_1(sK2))) )),
% 2.99/0.77    inference(resolution,[],[f282,f90])).
% 2.99/0.77  fof(f90,plain,(
% 2.99/0.77    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)) )),
% 2.99/0.77    inference(definition_unfolding,[],[f73,f61])).
% 2.99/0.77  fof(f61,plain,(
% 2.99/0.77    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.99/0.77    inference(cnf_transformation,[],[f16])).
% 2.99/0.77  fof(f16,axiom,(
% 2.99/0.77    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.99/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.99/0.77  fof(f73,plain,(
% 2.99/0.77    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 2.99/0.77    inference(cnf_transformation,[],[f33])).
% 2.99/0.77  fof(f33,plain,(
% 2.99/0.77    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.99/0.77    inference(ennf_transformation,[],[f5])).
% 2.99/0.77  fof(f5,axiom,(
% 2.99/0.77    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.99/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 2.99/0.77  fof(f282,plain,(
% 2.99/0.77    v1_relat_1(k2_funct_1(sK2))),
% 2.99/0.77    inference(resolution,[],[f258,f120])).
% 2.99/0.77  fof(f120,plain,(
% 2.99/0.77    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2))),
% 2.99/0.77    inference(resolution,[],[f57,f70])).
% 2.99/0.77  fof(f70,plain,(
% 2.99/0.77    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 2.99/0.77    inference(cnf_transformation,[],[f30])).
% 2.99/0.77  fof(f30,plain,(
% 2.99/0.77    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.99/0.77    inference(flattening,[],[f29])).
% 2.99/0.77  fof(f29,plain,(
% 2.99/0.77    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.99/0.77    inference(ennf_transformation,[],[f8])).
% 2.99/0.77  fof(f8,axiom,(
% 2.99/0.77    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.99/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.99/0.77  fof(f1980,plain,(
% 2.99/0.77    sK3 = k5_relat_1(k6_partfun1(sK1),k4_relat_1(sK2))),
% 2.99/0.77    inference(backward_demodulation,[],[f1821,f1877])).
% 2.99/0.77  fof(f1877,plain,(
% 2.99/0.77    k6_partfun1(sK1) = k5_relat_1(sK3,sK2)),
% 2.99/0.77    inference(backward_demodulation,[],[f1817,f1847])).
% 2.99/0.77  fof(f1847,plain,(
% 2.99/0.77    sK2 = k4_relat_1(sK3)),
% 2.99/0.77    inference(forward_demodulation,[],[f1815,f1846])).
% 2.99/0.77  fof(f1846,plain,(
% 2.99/0.77    sK2 = k7_relat_1(k4_relat_1(sK3),sK0)),
% 2.99/0.77    inference(forward_demodulation,[],[f1843,f296])).
% 2.99/0.77  fof(f296,plain,(
% 2.99/0.77    sK2 = k5_relat_1(sK2,k6_partfun1(sK1))),
% 2.99/0.77    inference(forward_demodulation,[],[f293,f277])).
% 2.99/0.77  fof(f277,plain,(
% 2.99/0.77    sK1 = k2_relat_1(sK2)),
% 2.99/0.77    inference(forward_demodulation,[],[f259,f51])).
% 2.99/0.77  fof(f51,plain,(
% 2.99/0.77    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.99/0.77    inference(cnf_transformation,[],[f23])).
% 2.99/0.77  fof(f259,plain,(
% 2.99/0.77    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 2.99/0.77    inference(resolution,[],[f59,f75])).
% 2.99/0.77  fof(f75,plain,(
% 2.99/0.77    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 2.99/0.77    inference(cnf_transformation,[],[f35])).
% 2.99/0.77  fof(f35,plain,(
% 2.99/0.77    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.99/0.77    inference(ennf_transformation,[],[f11])).
% 2.99/0.77  fof(f11,axiom,(
% 2.99/0.77    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.99/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.99/0.77  fof(f293,plain,(
% 2.99/0.77    sK2 = k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2)))),
% 2.99/0.77    inference(resolution,[],[f258,f89])).
% 2.99/0.77  fof(f89,plain,(
% 2.99/0.77    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0) )),
% 2.99/0.77    inference(definition_unfolding,[],[f66,f61])).
% 2.99/0.77  fof(f66,plain,(
% 2.99/0.77    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 2.99/0.77    inference(cnf_transformation,[],[f26])).
% 2.99/0.77  fof(f26,plain,(
% 2.99/0.77    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 2.99/0.77    inference(ennf_transformation,[],[f4])).
% 2.99/0.77  fof(f4,axiom,(
% 2.99/0.77    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 2.99/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 2.99/0.77  fof(f1843,plain,(
% 2.99/0.77    k5_relat_1(sK2,k6_partfun1(sK1)) = k7_relat_1(k4_relat_1(sK3),sK0)),
% 2.99/0.77    inference(backward_demodulation,[],[f1511,f1817])).
% 2.99/0.77  fof(f1511,plain,(
% 2.99/0.77    k5_relat_1(sK2,k5_relat_1(sK3,k4_relat_1(sK3))) = k7_relat_1(k4_relat_1(sK3),sK0)),
% 2.99/0.77    inference(backward_demodulation,[],[f1251,f1491])).
% 2.99/0.77  fof(f1491,plain,(
% 2.99/0.77    k2_funct_1(sK3) = k4_relat_1(sK3)),
% 2.99/0.77    inference(subsumption_resolution,[],[f1490,f48])).
% 2.99/0.77  fof(f48,plain,(
% 2.99/0.77    v1_funct_1(sK3)),
% 2.99/0.77    inference(cnf_transformation,[],[f23])).
% 2.99/0.77  fof(f1490,plain,(
% 2.99/0.77    ~v1_funct_1(sK3) | k2_funct_1(sK3) = k4_relat_1(sK3)),
% 2.99/0.77    inference(subsumption_resolution,[],[f1489,f197])).
% 2.99/0.77  fof(f197,plain,(
% 2.99/0.77    v1_relat_1(sK3)),
% 2.99/0.77    inference(resolution,[],[f50,f74])).
% 2.99/0.77  fof(f50,plain,(
% 2.99/0.77    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.99/0.77    inference(cnf_transformation,[],[f23])).
% 2.99/0.77  fof(f1489,plain,(
% 2.99/0.77    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | k2_funct_1(sK3) = k4_relat_1(sK3)),
% 2.99/0.77    inference(resolution,[],[f1484,f72])).
% 2.99/0.77  fof(f1484,plain,(
% 2.99/0.77    v2_funct_1(sK3)),
% 2.99/0.77    inference(subsumption_resolution,[],[f1483,f88])).
% 2.99/0.77  fof(f88,plain,(
% 2.99/0.77    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.99/0.77    inference(definition_unfolding,[],[f60,f61])).
% 2.99/0.77  fof(f60,plain,(
% 2.99/0.77    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.99/0.77    inference(cnf_transformation,[],[f9])).
% 2.99/0.77  fof(f9,axiom,(
% 2.99/0.77    ! [X0] : v2_funct_1(k6_relat_1(X0))),
% 2.99/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_funct_1)).
% 2.99/0.77  fof(f1483,plain,(
% 2.99/0.77    ~v2_funct_1(k6_partfun1(sK0)) | v2_funct_1(sK3)),
% 2.99/0.77    inference(forward_demodulation,[],[f1482,f1236])).
% 2.99/0.77  fof(f1236,plain,(
% 2.99/0.77    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.99/0.77    inference(backward_demodulation,[],[f793,f1198])).
% 2.99/0.77  fof(f1198,plain,(
% 2.99/0.77    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.99/0.77    inference(resolution,[],[f1197,f799])).
% 2.99/0.77  fof(f799,plain,(
% 2.99/0.77    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.99/0.77    inference(forward_demodulation,[],[f796,f793])).
% 2.99/0.77  fof(f796,plain,(
% 2.99/0.77    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.99/0.77    inference(backward_demodulation,[],[f313,f793])).
% 2.99/0.77  fof(f313,plain,(
% 2.99/0.77    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.99/0.77    inference(subsumption_resolution,[],[f311,f63])).
% 2.99/0.77  fof(f63,plain,(
% 2.99/0.77    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.99/0.77    inference(cnf_transformation,[],[f14])).
% 2.99/0.77  fof(f14,axiom,(
% 2.99/0.77    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.99/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.99/0.77  fof(f311,plain,(
% 2.99/0.77    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.99/0.77    inference(resolution,[],[f52,f84])).
% 2.99/0.77  fof(f84,plain,(
% 2.99/0.77    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 2.99/0.77    inference(cnf_transformation,[],[f43])).
% 2.99/0.77  fof(f43,plain,(
% 2.99/0.77    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.99/0.77    inference(flattening,[],[f42])).
% 2.99/0.77  fof(f42,plain,(
% 2.99/0.77    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.99/0.77    inference(ennf_transformation,[],[f12])).
% 2.99/0.77  fof(f12,axiom,(
% 2.99/0.77    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.99/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.99/0.77  fof(f52,plain,(
% 2.99/0.77    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.99/0.77    inference(cnf_transformation,[],[f23])).
% 2.99/0.77  fof(f1197,plain,(
% 2.99/0.77    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.99/0.77    inference(subsumption_resolution,[],[f1196,f50])).
% 2.99/0.77  fof(f1196,plain,(
% 2.99/0.77    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.99/0.77    inference(subsumption_resolution,[],[f1195,f48])).
% 2.99/0.77  fof(f1195,plain,(
% 2.99/0.77    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.99/0.77    inference(subsumption_resolution,[],[f1194,f59])).
% 2.99/0.77  fof(f1194,plain,(
% 2.99/0.77    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.99/0.77    inference(subsumption_resolution,[],[f1193,f57])).
% 2.99/0.77  fof(f1193,plain,(
% 2.99/0.77    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.99/0.77    inference(superposition,[],[f87,f793])).
% 2.99/0.77  fof(f87,plain,(
% 2.99/0.77    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))) )),
% 2.99/0.77    inference(cnf_transformation,[],[f47])).
% 2.99/0.77  fof(f47,plain,(
% 2.99/0.77    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.99/0.77    inference(flattening,[],[f46])).
% 2.99/0.77  fof(f46,plain,(
% 2.99/0.77    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.99/0.77    inference(ennf_transformation,[],[f13])).
% 2.99/0.77  fof(f13,axiom,(
% 2.99/0.77    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.99/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.99/0.77  fof(f793,plain,(
% 2.99/0.77    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.99/0.77    inference(subsumption_resolution,[],[f787,f57])).
% 2.99/0.77  fof(f787,plain,(
% 2.99/0.77    ~v1_funct_1(sK2) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.99/0.77    inference(resolution,[],[f222,f59])).
% 2.99/0.77  fof(f222,plain,(
% 2.99/0.77    ( ! [X12,X10,X11] : (~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) | ~v1_funct_1(X10) | k1_partfun1(X11,X12,sK1,sK0,X10,sK3) = k5_relat_1(X10,sK3)) )),
% 2.99/0.77    inference(subsumption_resolution,[],[f210,f48])).
% 2.99/0.77  fof(f210,plain,(
% 2.99/0.77    ( ! [X12,X10,X11] : (~v1_funct_1(X10) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) | ~v1_funct_1(sK3) | k1_partfun1(X11,X12,sK1,sK0,X10,sK3) = k5_relat_1(X10,sK3)) )),
% 2.99/0.77    inference(resolution,[],[f50,f85])).
% 2.99/0.77  fof(f85,plain,(
% 2.99/0.77    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 2.99/0.77    inference(cnf_transformation,[],[f45])).
% 2.99/0.77  fof(f45,plain,(
% 2.99/0.77    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.99/0.77    inference(flattening,[],[f44])).
% 2.99/0.77  fof(f44,plain,(
% 2.99/0.77    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.99/0.77    inference(ennf_transformation,[],[f15])).
% 2.99/0.77  fof(f15,axiom,(
% 2.99/0.77    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.99/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.99/0.77  fof(f1482,plain,(
% 2.99/0.77    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | v2_funct_1(sK3)),
% 2.99/0.77    inference(subsumption_resolution,[],[f1481,f54])).
% 2.99/0.77  fof(f54,plain,(
% 2.99/0.77    k1_xboole_0 != sK0),
% 2.99/0.77    inference(cnf_transformation,[],[f23])).
% 2.99/0.77  fof(f1481,plain,(
% 2.99/0.77    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | v2_funct_1(sK3)),
% 2.99/0.77    inference(subsumption_resolution,[],[f1480,f50])).
% 2.99/0.77  fof(f1480,plain,(
% 2.99/0.77    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | v2_funct_1(sK3)),
% 2.99/0.77    inference(subsumption_resolution,[],[f1479,f48])).
% 2.99/0.77  fof(f1479,plain,(
% 2.99/0.77    ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | v2_funct_1(sK3)),
% 2.99/0.77    inference(resolution,[],[f195,f49])).
% 2.99/0.77  fof(f49,plain,(
% 2.99/0.77    v1_funct_2(sK3,sK1,sK0)),
% 2.99/0.77    inference(cnf_transformation,[],[f23])).
% 2.99/0.77  fof(f195,plain,(
% 2.99/0.77    ( ! [X6,X7] : (~v1_funct_2(X6,sK1,X7) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6)) | k1_xboole_0 = X7 | v2_funct_1(X6)) )),
% 2.99/0.77    inference(subsumption_resolution,[],[f194,f51])).
% 2.99/0.77  fof(f194,plain,(
% 2.99/0.77    ( ! [X6,X7] : (~v1_funct_1(X6) | ~v1_funct_2(X6,sK1,X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6)) | sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = X7 | v2_funct_1(X6)) )),
% 2.99/0.77    inference(subsumption_resolution,[],[f193,f59])).
% 2.99/0.77  fof(f193,plain,(
% 2.99/0.77    ( ! [X6,X7] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X6) | ~v1_funct_2(X6,sK1,X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6)) | sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = X7 | v2_funct_1(X6)) )),
% 2.99/0.77    inference(subsumption_resolution,[],[f176,f57])).
% 2.99/0.77  fof(f176,plain,(
% 2.99/0.77    ( ! [X6,X7] : (~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X6) | ~v1_funct_2(X6,sK1,X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6)) | sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = X7 | v2_funct_1(X6)) )),
% 2.99/0.77    inference(resolution,[],[f58,f82])).
% 2.99/0.77  fof(f82,plain,(
% 2.99/0.77    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4)) )),
% 2.99/0.77    inference(cnf_transformation,[],[f41])).
% 2.99/0.77  fof(f41,plain,(
% 2.99/0.77    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.99/0.77    inference(flattening,[],[f40])).
% 2.99/0.77  fof(f40,plain,(
% 2.99/0.77    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.99/0.77    inference(ennf_transformation,[],[f18])).
% 2.99/0.77  fof(f18,axiom,(
% 2.99/0.77    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.99/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 2.99/0.77  fof(f58,plain,(
% 2.99/0.77    v1_funct_2(sK2,sK0,sK1)),
% 2.99/0.77    inference(cnf_transformation,[],[f23])).
% 2.99/0.77  fof(f1251,plain,(
% 2.99/0.77    k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) = k7_relat_1(k2_funct_1(sK3),sK0)),
% 2.99/0.77    inference(forward_demodulation,[],[f1230,f249])).
% 2.99/0.77  fof(f249,plain,(
% 2.99/0.77    ( ! [X6] : (k7_relat_1(k2_funct_1(sK3),X6) = k5_relat_1(k6_partfun1(X6),k2_funct_1(sK3))) )),
% 2.99/0.77    inference(resolution,[],[f225,f90])).
% 2.99/0.77  fof(f225,plain,(
% 2.99/0.77    v1_relat_1(k2_funct_1(sK3))),
% 2.99/0.77    inference(resolution,[],[f197,f95])).
% 2.99/0.77  fof(f95,plain,(
% 2.99/0.77    ~v1_relat_1(sK3) | v1_relat_1(k2_funct_1(sK3))),
% 2.99/0.77    inference(resolution,[],[f48,f70])).
% 2.99/0.77  fof(f1230,plain,(
% 2.99/0.77    k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))),
% 2.99/0.77    inference(backward_demodulation,[],[f619,f1198])).
% 2.99/0.77  fof(f619,plain,(
% 2.99/0.77    k5_relat_1(k5_relat_1(sK2,sK3),k2_funct_1(sK3)) = k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3)))),
% 2.99/0.77    inference(resolution,[],[f613,f225])).
% 2.99/0.77  fof(f613,plain,(
% 2.99/0.77    ( ! [X11] : (~v1_relat_1(X11) | k5_relat_1(k5_relat_1(sK2,sK3),X11) = k5_relat_1(sK2,k5_relat_1(sK3,X11))) )),
% 2.99/0.77    inference(resolution,[],[f231,f258])).
% 2.99/0.77  fof(f231,plain,(
% 2.99/0.77    ( ! [X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | k5_relat_1(k5_relat_1(X2,sK3),X3) = k5_relat_1(X2,k5_relat_1(sK3,X3))) )),
% 2.99/0.77    inference(resolution,[],[f197,f69])).
% 2.99/0.77  fof(f69,plain,(
% 2.99/0.77    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 2.99/0.77    inference(cnf_transformation,[],[f28])).
% 2.99/0.77  fof(f28,plain,(
% 2.99/0.77    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.99/0.77    inference(ennf_transformation,[],[f3])).
% 2.99/0.77  fof(f3,axiom,(
% 2.99/0.77    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.99/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 2.99/0.77  fof(f1815,plain,(
% 2.99/0.77    k4_relat_1(sK3) = k7_relat_1(k4_relat_1(sK3),sK0)),
% 2.99/0.77    inference(backward_demodulation,[],[f1516,f1807])).
% 2.99/0.77  fof(f1807,plain,(
% 2.99/0.77    sK0 = k2_relat_1(sK3)),
% 2.99/0.77    inference(subsumption_resolution,[],[f1806,f1238])).
% 2.99/0.77  fof(f1238,plain,(
% 2.99/0.77    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))),
% 2.99/0.77    inference(backward_demodulation,[],[f797,f1198])).
% 2.99/0.77  fof(f797,plain,(
% 2.99/0.77    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 2.99/0.77    inference(backward_demodulation,[],[f52,f793])).
% 2.99/0.77  fof(f1806,plain,(
% 2.99/0.77    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | sK0 = k2_relat_1(sK3)),
% 2.99/0.77    inference(forward_demodulation,[],[f1805,f1236])).
% 2.99/0.77  fof(f1805,plain,(
% 2.99/0.77    sK0 = k2_relat_1(sK3) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.99/0.77    inference(subsumption_resolution,[],[f1804,f59])).
% 2.99/0.77  fof(f1804,plain,(
% 2.99/0.77    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.99/0.77    inference(subsumption_resolution,[],[f1803,f57])).
% 2.99/0.77  fof(f1803,plain,(
% 2.99/0.77    ~v1_funct_1(sK2) | sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.99/0.77    inference(resolution,[],[f218,f58])).
% 2.99/0.77  fof(f218,plain,(
% 2.99/0.77    ( ! [X0] : (~v1_funct_2(X0,sK0,sK1) | ~v1_funct_1(X0) | sK0 = k2_relat_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0))) )),
% 2.99/0.77    inference(backward_demodulation,[],[f156,f198])).
% 2.99/0.77  fof(f198,plain,(
% 2.99/0.77    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)),
% 2.99/0.77    inference(resolution,[],[f50,f75])).
% 2.99/0.77  fof(f156,plain,(
% 2.99/0.77    ( ! [X0] : (~v1_funct_1(X0) | ~v1_funct_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3)) )),
% 2.99/0.77    inference(subsumption_resolution,[],[f155,f50])).
% 2.99/0.77  fof(f155,plain,(
% 2.99/0.77    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3)) )),
% 2.99/0.77    inference(subsumption_resolution,[],[f143,f48])).
% 2.99/0.77  fof(f143,plain,(
% 2.99/0.77    ( ! [X0] : (~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3)) )),
% 2.99/0.77    inference(resolution,[],[f49,f78])).
% 2.99/0.77  fof(f78,plain,(
% 2.99/0.77    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1) )),
% 2.99/0.77    inference(cnf_transformation,[],[f39])).
% 2.99/0.77  fof(f39,plain,(
% 2.99/0.77    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.99/0.77    inference(flattening,[],[f38])).
% 2.99/0.77  fof(f38,plain,(
% 2.99/0.77    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.99/0.77    inference(ennf_transformation,[],[f17])).
% 2.99/0.77  fof(f17,axiom,(
% 2.99/0.77    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.99/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 2.99/0.77  fof(f1516,plain,(
% 2.99/0.77    k4_relat_1(sK3) = k7_relat_1(k4_relat_1(sK3),k2_relat_1(sK3))),
% 2.99/0.77    inference(forward_demodulation,[],[f1496,f228])).
% 2.99/0.77  fof(f228,plain,(
% 2.99/0.77    k2_relat_1(sK3) = k1_relat_1(k4_relat_1(sK3))),
% 2.99/0.77    inference(resolution,[],[f197,f67])).
% 2.99/0.77  fof(f67,plain,(
% 2.99/0.77    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 2.99/0.77    inference(cnf_transformation,[],[f27])).
% 2.99/0.77  fof(f27,plain,(
% 2.99/0.77    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.99/0.77    inference(ennf_transformation,[],[f2])).
% 2.99/0.77  fof(f2,axiom,(
% 2.99/0.77    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 2.99/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 2.99/0.77  fof(f1496,plain,(
% 2.99/0.77    k4_relat_1(sK3) = k7_relat_1(k4_relat_1(sK3),k1_relat_1(k4_relat_1(sK3)))),
% 2.99/0.77    inference(backward_demodulation,[],[f239,f1491])).
% 2.99/0.77  fof(f239,plain,(
% 2.99/0.77    k2_funct_1(sK3) = k7_relat_1(k2_funct_1(sK3),k1_relat_1(k2_funct_1(sK3)))),
% 2.99/0.77    inference(resolution,[],[f225,f65])).
% 2.99/0.77  fof(f65,plain,(
% 2.99/0.77    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 2.99/0.77    inference(cnf_transformation,[],[f25])).
% 2.99/0.77  fof(f25,plain,(
% 2.99/0.77    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 2.99/0.77    inference(ennf_transformation,[],[f6])).
% 2.99/0.77  fof(f6,axiom,(
% 2.99/0.77    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 2.99/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 2.99/0.77  fof(f1817,plain,(
% 2.99/0.77    k6_partfun1(sK1) = k5_relat_1(sK3,k4_relat_1(sK3))),
% 2.99/0.77    inference(trivial_inequality_removal,[],[f1814])).
% 2.99/0.77  fof(f1814,plain,(
% 2.99/0.77    sK0 != sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k4_relat_1(sK3))),
% 2.99/0.77    inference(backward_demodulation,[],[f1515,f1807])).
% 2.99/0.77  fof(f1515,plain,(
% 2.99/0.77    sK0 != k2_relat_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k4_relat_1(sK3))),
% 2.99/0.77    inference(subsumption_resolution,[],[f1494,f1484])).
% 2.99/0.77  fof(f1494,plain,(
% 2.99/0.77    k6_partfun1(sK1) = k5_relat_1(sK3,k4_relat_1(sK3)) | ~v2_funct_1(sK3) | sK0 != k2_relat_1(sK3)),
% 2.99/0.77    inference(backward_demodulation,[],[f220,f1491])).
% 2.99/0.77  fof(f220,plain,(
% 2.99/0.77    ~v2_funct_1(sK3) | sK0 != k2_relat_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.99/0.77    inference(backward_demodulation,[],[f151,f198])).
% 2.99/0.77  fof(f151,plain,(
% 2.99/0.77    sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.99/0.77    inference(subsumption_resolution,[],[f150,f54])).
% 2.99/0.77  fof(f150,plain,(
% 2.99/0.77    sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.99/0.77    inference(subsumption_resolution,[],[f149,f50])).
% 2.99/0.77  fof(f149,plain,(
% 2.99/0.77    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.99/0.77    inference(subsumption_resolution,[],[f141,f48])).
% 2.99/0.77  fof(f141,plain,(
% 2.99/0.77    ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.99/0.77    inference(resolution,[],[f49,f76])).
% 2.99/0.77  fof(f76,plain,(
% 2.99/0.77    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 2.99/0.77    inference(cnf_transformation,[],[f37])).
% 2.99/0.77  fof(f37,plain,(
% 2.99/0.77    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.99/0.77    inference(flattening,[],[f36])).
% 2.99/0.77  fof(f36,plain,(
% 2.99/0.77    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.99/0.77    inference(ennf_transformation,[],[f19])).
% 2.99/0.77  fof(f19,axiom,(
% 2.99/0.77    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.99/0.77    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 2.99/0.77  fof(f1821,plain,(
% 2.99/0.77    sK3 = k5_relat_1(k5_relat_1(sK3,sK2),k4_relat_1(sK2))),
% 2.99/0.77    inference(backward_demodulation,[],[f473,f1812])).
% 2.99/0.77  fof(f1812,plain,(
% 2.99/0.77    sK3 = k5_relat_1(sK3,k6_partfun1(sK0))),
% 2.99/0.77    inference(backward_demodulation,[],[f236,f1807])).
% 2.99/0.77  fof(f236,plain,(
% 2.99/0.77    sK3 = k5_relat_1(sK3,k6_partfun1(k2_relat_1(sK3)))),
% 2.99/0.77    inference(resolution,[],[f197,f89])).
% 2.99/0.77  fof(f473,plain,(
% 2.99/0.77    k5_relat_1(k5_relat_1(sK3,sK2),k4_relat_1(sK2)) = k5_relat_1(sK3,k6_partfun1(sK0))),
% 2.99/0.77    inference(forward_demodulation,[],[f467,f324])).
% 2.99/0.77  fof(f324,plain,(
% 2.99/0.77    k6_partfun1(sK0) = k5_relat_1(sK2,k4_relat_1(sK2))),
% 2.99/0.77    inference(backward_demodulation,[],[f182,f321])).
% 2.99/0.77  fof(f182,plain,(
% 2.99/0.77    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.99/0.77    inference(subsumption_resolution,[],[f181,f55])).
% 2.99/0.77  fof(f55,plain,(
% 2.99/0.77    k1_xboole_0 != sK1),
% 2.99/0.77    inference(cnf_transformation,[],[f23])).
% 2.99/0.77  fof(f181,plain,(
% 2.99/0.77    k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.99/0.77    inference(subsumption_resolution,[],[f180,f53])).
% 2.99/0.77  fof(f180,plain,(
% 2.99/0.77    ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.99/0.77    inference(subsumption_resolution,[],[f179,f51])).
% 2.99/0.77  fof(f179,plain,(
% 2.99/0.77    sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.99/0.77    inference(subsumption_resolution,[],[f178,f59])).
% 2.99/0.77  fof(f178,plain,(
% 2.99/0.77    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.99/0.77    inference(subsumption_resolution,[],[f170,f57])).
% 2.99/0.77  fof(f170,plain,(
% 2.99/0.77    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.99/0.77    inference(resolution,[],[f58,f76])).
% 2.99/0.77  fof(f467,plain,(
% 2.99/0.77    k5_relat_1(k5_relat_1(sK3,sK2),k4_relat_1(sK2)) = k5_relat_1(sK3,k5_relat_1(sK2,k4_relat_1(sK2)))),
% 2.99/0.77    inference(resolution,[],[f463,f326])).
% 2.99/0.77  fof(f326,plain,(
% 2.99/0.77    v1_relat_1(k4_relat_1(sK2))),
% 2.99/0.77    inference(backward_demodulation,[],[f282,f321])).
% 2.99/0.77  fof(f463,plain,(
% 2.99/0.77    ( ! [X11] : (~v1_relat_1(X11) | k5_relat_1(k5_relat_1(sK3,sK2),X11) = k5_relat_1(sK3,k5_relat_1(sK2,X11))) )),
% 2.99/0.77    inference(resolution,[],[f230,f258])).
% 2.99/0.77  fof(f230,plain,(
% 2.99/0.77    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | k5_relat_1(k5_relat_1(sK3,X0),X1) = k5_relat_1(sK3,k5_relat_1(X0,X1))) )),
% 2.99/0.77    inference(resolution,[],[f197,f69])).
% 2.99/0.77  fof(f335,plain,(
% 2.99/0.77    k4_relat_1(sK2) = k7_relat_1(k4_relat_1(sK2),sK1)),
% 2.99/0.77    inference(forward_demodulation,[],[f327,f295])).
% 2.99/0.77  fof(f295,plain,(
% 2.99/0.77    sK1 = k1_relat_1(k4_relat_1(sK2))),
% 2.99/0.77    inference(forward_demodulation,[],[f285,f277])).
% 2.99/0.77  fof(f285,plain,(
% 2.99/0.77    k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))),
% 2.99/0.77    inference(resolution,[],[f258,f67])).
% 2.99/0.77  fof(f327,plain,(
% 2.99/0.77    k4_relat_1(sK2) = k7_relat_1(k4_relat_1(sK2),k1_relat_1(k4_relat_1(sK2)))),
% 2.99/0.77    inference(backward_demodulation,[],[f298,f321])).
% 2.99/0.77  fof(f298,plain,(
% 2.99/0.77    k2_funct_1(sK2) = k7_relat_1(k2_funct_1(sK2),k1_relat_1(k2_funct_1(sK2)))),
% 2.99/0.77    inference(resolution,[],[f282,f65])).
% 2.99/0.77  % SZS output end Proof for theBenchmark
% 2.99/0.77  % (10362)------------------------------
% 2.99/0.77  % (10362)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.99/0.77  % (10362)Termination reason: Refutation
% 2.99/0.77  
% 2.99/0.77  % (10362)Memory used [KB]: 2686
% 2.99/0.77  % (10362)Time elapsed: 0.328 s
% 2.99/0.77  % (10362)------------------------------
% 2.99/0.77  % (10362)------------------------------
% 2.99/0.77  % (10344)Success in time 0.405 s
%------------------------------------------------------------------------------
