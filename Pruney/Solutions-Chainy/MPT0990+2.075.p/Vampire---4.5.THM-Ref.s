%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:41 EST 2020

% Result     : Theorem 2.21s
% Output     : Refutation 2.21s
% Verified   : 
% Statistics : Number of formulae       :  182 (2228 expanded)
%              Number of leaves         :   20 ( 407 expanded)
%              Depth                    :   30
%              Number of atoms          :  682 (16660 expanded)
%              Number of equality atoms :  177 (5170 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4868,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4773,f61])).

fof(f61,plain,(
    sK3 != k2_funct_1(sK2) ),
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).

fof(f4773,plain,(
    sK3 = k2_funct_1(sK2) ),
    inference(backward_demodulation,[],[f2782,f4767])).

fof(f4767,plain,(
    sK2 = k2_funct_1(sK3) ),
    inference(forward_demodulation,[],[f4766,f425])).

fof(f425,plain,(
    sK2 = k5_relat_1(sK2,k6_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f408,f400])).

fof(f400,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f379,f56])).

fof(f56,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f379,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f64,f82])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f408,plain,(
    sK2 = k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2))) ),
    inference(resolution,[],[f378,f68])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f378,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f64,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f4766,plain,(
    k2_funct_1(sK3) = k5_relat_1(sK2,k6_relat_1(sK1)) ),
    inference(forward_demodulation,[],[f4765,f3064])).

fof(f3064,plain,(
    k2_funct_1(sK3) = k5_relat_1(k6_relat_1(sK0),k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f2785,f3049])).

fof(f3049,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f3048,f2691])).

fof(f2691,plain,(
    r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f1391,f2658])).

fof(f2658,plain,(
    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f2649,f1393])).

fof(f1393,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(forward_demodulation,[],[f1390,f1387])).

fof(f1387,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f1378,f62])).

fof(f62,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f1378,plain,
    ( ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f329,f64])).

fof(f329,plain,(
    ! [X10,X11,X9] :
      ( ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ v1_funct_1(X9)
      | k1_partfun1(X10,X11,sK1,sK0,X9,sK3) = k5_relat_1(X9,sK3) ) ),
    inference(subsumption_resolution,[],[f311,f53])).

fof(f53,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f311,plain,(
    ! [X10,X11,X9] :
      ( ~ v1_funct_1(X9)
      | ~ m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11)))
      | ~ v1_funct_1(sK3)
      | k1_partfun1(X10,X11,sK1,sK0,X9,sK3) = k5_relat_1(X9,sK3) ) ),
    inference(resolution,[],[f55,f95])).

fof(f95,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f1390,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(backward_demodulation,[],[f429,f1387])).

fof(f429,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    inference(subsumption_resolution,[],[f427,f99])).

fof(f99,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f67,f65])).

fof(f65,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f427,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    inference(resolution,[],[f98,f94])).

fof(f94,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f98,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    inference(definition_unfolding,[],[f57,f65])).

fof(f57,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f2649,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f2648,f55])).

fof(f2648,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f2647,f53])).

fof(f2647,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f2646,f64])).

fof(f2646,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f2645,f62])).

fof(f2645,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f97,f1387])).

fof(f97,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f1391,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) ),
    inference(backward_demodulation,[],[f98,f1387])).

fof(f3048,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))
    | sK0 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f3047,f2689])).

fof(f2689,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    inference(backward_demodulation,[],[f1387,f2658])).

fof(f3047,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f3046,f64])).

fof(f3046,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f3043,f62])).

fof(f3043,plain,
    ( ~ v1_funct_1(sK2)
    | sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    inference(resolution,[],[f327,f63])).

fof(f63,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f327,plain,(
    ! [X8] :
      ( ~ v1_funct_2(X8,sK0,sK1)
      | ~ v1_funct_1(X8)
      | sK0 = k2_relat_1(sK3)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X8,sK3),k6_relat_1(sK0)) ) ),
    inference(backward_demodulation,[],[f226,f300])).

fof(f300,plain,(
    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f55,f82])).

fof(f226,plain,(
    ! [X8] :
      ( ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,sK0,sK1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X8,sK3),k6_relat_1(sK0))
      | sK0 = k2_relset_1(sK1,sK0,sK3) ) ),
    inference(subsumption_resolution,[],[f225,f55])).

fof(f225,plain,(
    ! [X8] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,sK0,sK1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X8,sK3),k6_relat_1(sK0))
      | sK0 = k2_relset_1(sK1,sK0,sK3) ) ),
    inference(subsumption_resolution,[],[f203,f53])).

fof(f203,plain,(
    ! [X8] :
      ( ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_1(X8)
      | ~ v1_funct_2(X8,sK0,sK1)
      | ~ m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X8,sK3),k6_relat_1(sK0))
      | sK0 = k2_relset_1(sK1,sK0,sK3) ) ),
    inference(resolution,[],[f54,f103])).

fof(f103,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1))
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(definition_unfolding,[],[f88,f65])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).

fof(f54,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f2785,plain,(
    k2_funct_1(sK3) = k5_relat_1(k6_relat_1(k2_relat_1(sK3)),k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f352,f2784])).

fof(f2784,plain,(
    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f2783,f53])).

fof(f2783,plain,
    ( ~ v1_funct_1(sK3)
    | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f2760,f299])).

fof(f299,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f55,f81])).

fof(f2760,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f2695,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f2695,plain,(
    v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f2693,f547])).

fof(f547,plain,(
    v2_funct_1(k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f546,f58])).

fof(f58,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f546,plain,
    ( v2_funct_1(k6_relat_1(sK0))
    | ~ v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f545,f62])).

fof(f545,plain,
    ( v2_funct_1(k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f540,f378])).

fof(f540,plain,
    ( v2_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2) ),
    inference(resolution,[],[f539,f73])).

fof(f73,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | v2_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f539,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | v2_funct_1(k6_relat_1(sK0)) ),
    inference(subsumption_resolution,[],[f538,f243])).

fof(f243,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f242,f56])).

fof(f242,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f241,f58])).

fof(f241,plain,
    ( ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f240,f64])).

fof(f240,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f229,f62])).

fof(f229,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f63,f83])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f538,plain,
    ( v2_funct_1(k6_relat_1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f537,f407])).

fof(f407,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f378,f164])).

fof(f164,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f62,f74])).

fof(f74,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f537,plain,
    ( v2_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f536,f58])).

fof(f536,plain,
    ( v2_funct_1(k6_relat_1(sK0))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f535,f62])).

fof(f535,plain,
    ( v2_funct_1(k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f533,f378])).

fof(f533,plain,
    ( v2_funct_1(k6_relat_1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f80,f263])).

fof(f263,plain,(
    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f262,f60])).

fof(f60,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f262,plain,
    ( k1_xboole_0 = sK1
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f261,f58])).

fof(f261,plain,
    ( ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f260,f56])).

fof(f260,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f259,f64])).

fof(f259,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f237,f62])).

fof(f237,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(resolution,[],[f63,f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(definition_unfolding,[],[f86,f65])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v2_funct_1(X1)
      | v2_funct_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) )
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v2_funct_1(X1)
        & v1_funct_1(X1)
        & v1_relat_1(X1)
        & v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k5_relat_1(X0,X1))
        & v1_relat_1(k5_relat_1(X0,X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_funct_1)).

fof(f2693,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | v2_funct_1(sK3) ),
    inference(backward_demodulation,[],[f2221,f2658])).

fof(f2221,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | v2_funct_1(sK3) ),
    inference(forward_demodulation,[],[f2220,f1387])).

fof(f2220,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f2219,f59])).

fof(f59,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f23])).

fof(f2219,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f2218,f55])).

fof(f2218,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f2215,f53])).

fof(f2215,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK3) ),
    inference(resolution,[],[f253,f54])).

fof(f253,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_2(X4,sK1,X5)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,X5)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X5,sK2,X4))
      | k1_xboole_0 = X5
      | v2_funct_1(X4) ) ),
    inference(subsumption_resolution,[],[f252,f56])).

fof(f252,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,sK1,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,X5)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X5,sK2,X4))
      | sK1 != k2_relset_1(sK0,sK1,sK2)
      | k1_xboole_0 = X5
      | v2_funct_1(X4) ) ),
    inference(subsumption_resolution,[],[f251,f64])).

fof(f251,plain,(
    ! [X4,X5] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,sK1,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,X5)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X5,sK2,X4))
      | sK1 != k2_relset_1(sK0,sK1,sK2)
      | k1_xboole_0 = X5
      | v2_funct_1(X4) ) ),
    inference(subsumption_resolution,[],[f234,f62])).

fof(f234,plain,(
    ! [X4,X5] :
      ( ~ v1_funct_1(sK2)
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_2(X4,sK1,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,X5)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X5,sK2,X4))
      | sK1 != k2_relset_1(sK0,sK1,sK2)
      | k1_xboole_0 = X5
      | v2_funct_1(X4) ) ),
    inference(resolution,[],[f63,f92])).

fof(f92,plain,(
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
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
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
    inference(flattening,[],[f45])).

fof(f45,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).

fof(f352,plain,(
    k2_funct_1(sK3) = k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3)) ),
    inference(resolution,[],[f349,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).

fof(f349,plain,(
    v1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f111,f299])).

fof(f111,plain,
    ( ~ v1_relat_1(sK3)
    | v1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f53,f74])).

fof(f4765,plain,(
    k5_relat_1(sK2,k6_relat_1(sK1)) = k5_relat_1(k6_relat_1(sK0),k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f4756,f3079])).

fof(f3079,plain,(
    k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f3070,f2695])).

fof(f3070,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(trivial_inequality_removal,[],[f3056])).

fof(f3056,plain,
    ( sK0 != sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f326,f3049])).

fof(f326,plain,
    ( ~ v2_funct_1(sK3)
    | sK0 != k2_relat_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f224,f300])).

fof(f224,plain,
    ( sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f223,f59])).

fof(f223,plain,
    ( sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f222,f55])).

fof(f222,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f202,f53])).

fof(f202,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(resolution,[],[f54,f102])).

fof(f4756,plain,(
    k5_relat_1(k6_relat_1(sK0),k2_funct_1(sK3)) = k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) ),
    inference(resolution,[],[f4715,f349])).

fof(f4715,plain,(
    ! [X48] :
      ( ~ v1_relat_1(X48)
      | k5_relat_1(sK2,k5_relat_1(sK3,X48)) = k5_relat_1(k6_relat_1(sK0),X48) ) ),
    inference(forward_demodulation,[],[f4712,f2658])).

fof(f4712,plain,(
    ! [X48] :
      ( ~ v1_relat_1(X48)
      | k5_relat_1(k5_relat_1(sK2,sK3),X48) = k5_relat_1(sK2,k5_relat_1(sK3,X48)) ) ),
    inference(resolution,[],[f335,f378])).

fof(f335,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(X2,sK3),X3) = k5_relat_1(X2,k5_relat_1(sK3,X3)) ) ),
    inference(resolution,[],[f299,f70])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f2782,plain,(
    sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f2781,f53])).

fof(f2781,plain,
    ( ~ v1_funct_1(sK3)
    | sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f2759,f299])).

fof(f2759,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f2695,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 15:35:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.50  % (15157)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.51  % (15179)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.51  % (15155)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.51  % (15174)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.21/0.51  % (15170)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.51  % (15163)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.21/0.51  % (15165)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.51  % (15158)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.51  % (15166)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.52  % (15153)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.52  % (15181)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.52  % (15160)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (15177)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.52  % (15170)Refutation not found, incomplete strategy% (15170)------------------------------
% 0.21/0.52  % (15170)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (15169)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.53  % (15152)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.53  % (15170)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.53  
% 0.21/0.53  % (15170)Memory used [KB]: 10746
% 0.21/0.53  % (15170)Time elapsed: 0.126 s
% 0.21/0.53  % (15170)------------------------------
% 0.21/0.53  % (15170)------------------------------
% 0.21/0.53  % (15183)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.53  % (15182)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (15180)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.53  % (15175)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.21/0.54  % (15156)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.54  % (15176)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.54  % (15171)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.54  % (15168)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.54  % (15172)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (15164)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.54  % (15167)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.21/0.54  % (15173)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (15162)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.55  % (15184)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.21/0.55  % (15161)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 2.21/0.66  % (15273)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.21/0.70  % (15171)Refutation found. Thanks to Tanya!
% 2.21/0.70  % SZS status Theorem for theBenchmark
% 2.21/0.70  % SZS output start Proof for theBenchmark
% 2.21/0.70  fof(f4868,plain,(
% 2.21/0.70    $false),
% 2.21/0.70    inference(subsumption_resolution,[],[f4773,f61])).
% 2.21/0.70  fof(f61,plain,(
% 2.21/0.70    sK3 != k2_funct_1(sK2)),
% 2.21/0.70    inference(cnf_transformation,[],[f23])).
% 2.21/0.70  fof(f23,plain,(
% 2.21/0.70    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.21/0.70    inference(flattening,[],[f22])).
% 2.21/0.70  fof(f22,plain,(
% 2.21/0.70    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.21/0.70    inference(ennf_transformation,[],[f21])).
% 2.21/0.70  fof(f21,negated_conjecture,(
% 2.21/0.70    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.21/0.70    inference(negated_conjecture,[],[f20])).
% 2.21/0.70  fof(f20,conjecture,(
% 2.21/0.70    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.21/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.21/0.70  fof(f4773,plain,(
% 2.21/0.70    sK3 = k2_funct_1(sK2)),
% 2.21/0.70    inference(backward_demodulation,[],[f2782,f4767])).
% 2.21/0.70  fof(f4767,plain,(
% 2.21/0.70    sK2 = k2_funct_1(sK3)),
% 2.21/0.70    inference(forward_demodulation,[],[f4766,f425])).
% 2.21/0.70  fof(f425,plain,(
% 2.21/0.70    sK2 = k5_relat_1(sK2,k6_relat_1(sK1))),
% 2.21/0.70    inference(forward_demodulation,[],[f408,f400])).
% 2.21/0.70  fof(f400,plain,(
% 2.21/0.70    sK1 = k2_relat_1(sK2)),
% 2.21/0.70    inference(forward_demodulation,[],[f379,f56])).
% 2.21/0.70  fof(f56,plain,(
% 2.21/0.70    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.21/0.70    inference(cnf_transformation,[],[f23])).
% 2.21/0.70  fof(f379,plain,(
% 2.21/0.70    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 2.21/0.70    inference(resolution,[],[f64,f82])).
% 2.21/0.70  fof(f82,plain,(
% 2.21/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 2.21/0.70    inference(cnf_transformation,[],[f38])).
% 2.21/0.70  fof(f38,plain,(
% 2.21/0.70    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/0.70    inference(ennf_transformation,[],[f10])).
% 2.21/0.70  fof(f10,axiom,(
% 2.21/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.21/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.21/0.70  fof(f64,plain,(
% 2.21/0.70    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.21/0.70    inference(cnf_transformation,[],[f23])).
% 2.21/0.70  fof(f408,plain,(
% 2.21/0.70    sK2 = k5_relat_1(sK2,k6_relat_1(k2_relat_1(sK2)))),
% 2.21/0.70    inference(resolution,[],[f378,f68])).
% 2.21/0.70  fof(f68,plain,(
% 2.21/0.70    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 2.21/0.70    inference(cnf_transformation,[],[f24])).
% 2.21/0.70  fof(f24,plain,(
% 2.21/0.70    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 2.21/0.70    inference(ennf_transformation,[],[f3])).
% 2.21/0.70  fof(f3,axiom,(
% 2.21/0.70    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 2.21/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 2.21/0.70  fof(f378,plain,(
% 2.21/0.70    v1_relat_1(sK2)),
% 2.21/0.70    inference(resolution,[],[f64,f81])).
% 2.21/0.70  fof(f81,plain,(
% 2.21/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.21/0.70    inference(cnf_transformation,[],[f37])).
% 2.21/0.70  fof(f37,plain,(
% 2.21/0.70    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/0.70    inference(ennf_transformation,[],[f9])).
% 2.21/0.70  fof(f9,axiom,(
% 2.21/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.21/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.21/0.70  fof(f4766,plain,(
% 2.21/0.70    k2_funct_1(sK3) = k5_relat_1(sK2,k6_relat_1(sK1))),
% 2.21/0.70    inference(forward_demodulation,[],[f4765,f3064])).
% 2.21/0.70  fof(f3064,plain,(
% 2.21/0.70    k2_funct_1(sK3) = k5_relat_1(k6_relat_1(sK0),k2_funct_1(sK3))),
% 2.21/0.70    inference(backward_demodulation,[],[f2785,f3049])).
% 2.21/0.70  fof(f3049,plain,(
% 2.21/0.70    sK0 = k2_relat_1(sK3)),
% 2.21/0.70    inference(subsumption_resolution,[],[f3048,f2691])).
% 2.21/0.70  fof(f2691,plain,(
% 2.21/0.70    r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0))),
% 2.21/0.70    inference(backward_demodulation,[],[f1391,f2658])).
% 2.21/0.70  fof(f2658,plain,(
% 2.21/0.70    k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 2.21/0.70    inference(resolution,[],[f2649,f1393])).
% 2.21/0.70  fof(f1393,plain,(
% 2.21/0.70    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 2.21/0.70    inference(forward_demodulation,[],[f1390,f1387])).
% 2.21/0.70  fof(f1387,plain,(
% 2.21/0.70    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.21/0.70    inference(subsumption_resolution,[],[f1378,f62])).
% 2.21/0.70  fof(f62,plain,(
% 2.21/0.70    v1_funct_1(sK2)),
% 2.21/0.70    inference(cnf_transformation,[],[f23])).
% 2.21/0.70  fof(f1378,plain,(
% 2.21/0.70    ~v1_funct_1(sK2) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.21/0.70    inference(resolution,[],[f329,f64])).
% 2.21/0.70  fof(f329,plain,(
% 2.21/0.70    ( ! [X10,X11,X9] : (~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | ~v1_funct_1(X9) | k1_partfun1(X10,X11,sK1,sK0,X9,sK3) = k5_relat_1(X9,sK3)) )),
% 2.21/0.70    inference(subsumption_resolution,[],[f311,f53])).
% 2.21/0.70  fof(f53,plain,(
% 2.21/0.70    v1_funct_1(sK3)),
% 2.21/0.70    inference(cnf_transformation,[],[f23])).
% 2.21/0.70  fof(f311,plain,(
% 2.21/0.70    ( ! [X10,X11,X9] : (~v1_funct_1(X9) | ~m1_subset_1(X9,k1_zfmisc_1(k2_zfmisc_1(X10,X11))) | ~v1_funct_1(sK3) | k1_partfun1(X10,X11,sK1,sK0,X9,sK3) = k5_relat_1(X9,sK3)) )),
% 2.21/0.70    inference(resolution,[],[f55,f95])).
% 2.21/0.70  fof(f95,plain,(
% 2.21/0.70    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 2.21/0.70    inference(cnf_transformation,[],[f50])).
% 2.21/0.70  fof(f50,plain,(
% 2.21/0.70    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.21/0.70    inference(flattening,[],[f49])).
% 2.21/0.70  fof(f49,plain,(
% 2.21/0.70    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.21/0.70    inference(ennf_transformation,[],[f14])).
% 2.21/0.70  fof(f14,axiom,(
% 2.21/0.70    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.21/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.21/0.70  fof(f55,plain,(
% 2.21/0.70    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.21/0.70    inference(cnf_transformation,[],[f23])).
% 2.21/0.70  fof(f1390,plain,(
% 2.21/0.70    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.21/0.70    inference(backward_demodulation,[],[f429,f1387])).
% 2.21/0.70  fof(f429,plain,(
% 2.21/0.70    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 2.21/0.70    inference(subsumption_resolution,[],[f427,f99])).
% 2.21/0.70  fof(f99,plain,(
% 2.21/0.70    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.21/0.70    inference(definition_unfolding,[],[f67,f65])).
% 2.21/0.70  fof(f65,plain,(
% 2.21/0.70    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 2.21/0.70    inference(cnf_transformation,[],[f15])).
% 2.21/0.70  fof(f15,axiom,(
% 2.21/0.70    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 2.21/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.21/0.70  fof(f67,plain,(
% 2.21/0.70    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.21/0.70    inference(cnf_transformation,[],[f13])).
% 2.21/0.70  fof(f13,axiom,(
% 2.21/0.70    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.21/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.21/0.70  fof(f427,plain,(
% 2.21/0.70    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k6_relat_1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 2.21/0.70    inference(resolution,[],[f98,f94])).
% 2.21/0.70  fof(f94,plain,(
% 2.21/0.70    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 2.21/0.70    inference(cnf_transformation,[],[f48])).
% 2.21/0.70  fof(f48,plain,(
% 2.21/0.70    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.21/0.70    inference(flattening,[],[f47])).
% 2.21/0.70  fof(f47,plain,(
% 2.21/0.70    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.21/0.70    inference(ennf_transformation,[],[f11])).
% 2.21/0.70  fof(f11,axiom,(
% 2.21/0.70    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.21/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.21/0.70  fof(f98,plain,(
% 2.21/0.70    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 2.21/0.70    inference(definition_unfolding,[],[f57,f65])).
% 2.21/0.70  fof(f57,plain,(
% 2.21/0.70    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.21/0.70    inference(cnf_transformation,[],[f23])).
% 2.21/0.70  fof(f2649,plain,(
% 2.21/0.70    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.21/0.70    inference(subsumption_resolution,[],[f2648,f55])).
% 2.21/0.70  fof(f2648,plain,(
% 2.21/0.70    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.21/0.70    inference(subsumption_resolution,[],[f2647,f53])).
% 2.21/0.70  fof(f2647,plain,(
% 2.21/0.70    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.21/0.70    inference(subsumption_resolution,[],[f2646,f64])).
% 2.21/0.70  fof(f2646,plain,(
% 2.21/0.70    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.21/0.70    inference(subsumption_resolution,[],[f2645,f62])).
% 2.21/0.70  fof(f2645,plain,(
% 2.21/0.70    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.21/0.70    inference(superposition,[],[f97,f1387])).
% 2.21/0.70  fof(f97,plain,(
% 2.21/0.70    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))) )),
% 2.21/0.70    inference(cnf_transformation,[],[f52])).
% 2.21/0.70  fof(f52,plain,(
% 2.21/0.70    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.21/0.70    inference(flattening,[],[f51])).
% 2.21/0.70  fof(f51,plain,(
% 2.21/0.70    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.21/0.70    inference(ennf_transformation,[],[f12])).
% 2.21/0.70  fof(f12,axiom,(
% 2.21/0.70    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.21/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.21/0.70  fof(f1391,plain,(
% 2.21/0.70    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))),
% 2.21/0.70    inference(backward_demodulation,[],[f98,f1387])).
% 2.21/0.70  fof(f3048,plain,(
% 2.21/0.70    ~r2_relset_1(sK0,sK0,k6_relat_1(sK0),k6_relat_1(sK0)) | sK0 = k2_relat_1(sK3)),
% 2.21/0.70    inference(forward_demodulation,[],[f3047,f2689])).
% 2.21/0.70  fof(f2689,plain,(
% 2.21/0.70    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 2.21/0.70    inference(backward_demodulation,[],[f1387,f2658])).
% 2.21/0.70  fof(f3047,plain,(
% 2.21/0.70    sK0 = k2_relat_1(sK3) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 2.21/0.70    inference(subsumption_resolution,[],[f3046,f64])).
% 2.21/0.70  fof(f3046,plain,(
% 2.21/0.70    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 2.21/0.70    inference(subsumption_resolution,[],[f3043,f62])).
% 2.21/0.70  fof(f3043,plain,(
% 2.21/0.70    ~v1_funct_1(sK2) | sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 2.21/0.70    inference(resolution,[],[f327,f63])).
% 2.21/0.70  fof(f63,plain,(
% 2.21/0.70    v1_funct_2(sK2,sK0,sK1)),
% 2.21/0.70    inference(cnf_transformation,[],[f23])).
% 2.21/0.70  fof(f327,plain,(
% 2.21/0.70    ( ! [X8] : (~v1_funct_2(X8,sK0,sK1) | ~v1_funct_1(X8) | sK0 = k2_relat_1(sK3) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X8,sK3),k6_relat_1(sK0))) )),
% 2.21/0.70    inference(backward_demodulation,[],[f226,f300])).
% 2.21/0.70  fof(f300,plain,(
% 2.21/0.70    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)),
% 2.21/0.70    inference(resolution,[],[f55,f82])).
% 2.21/0.70  fof(f226,plain,(
% 2.21/0.70    ( ! [X8] : (~v1_funct_1(X8) | ~v1_funct_2(X8,sK0,sK1) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X8,sK3),k6_relat_1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3)) )),
% 2.21/0.70    inference(subsumption_resolution,[],[f225,f55])).
% 2.21/0.70  fof(f225,plain,(
% 2.21/0.70    ( ! [X8] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,sK0,sK1) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X8,sK3),k6_relat_1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3)) )),
% 2.21/0.70    inference(subsumption_resolution,[],[f203,f53])).
% 2.21/0.70  fof(f203,plain,(
% 2.21/0.70    ( ! [X8] : (~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(X8) | ~v1_funct_2(X8,sK0,sK1) | ~m1_subset_1(X8,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X8,sK3),k6_relat_1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3)) )),
% 2.21/0.70    inference(resolution,[],[f54,f103])).
% 2.21/0.70  fof(f103,plain,(
% 2.21/0.70    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1)) | k2_relset_1(X0,X1,X2) = X1) )),
% 2.21/0.70    inference(definition_unfolding,[],[f88,f65])).
% 2.21/0.70  fof(f88,plain,(
% 2.21/0.70    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1) )),
% 2.21/0.70    inference(cnf_transformation,[],[f44])).
% 2.21/0.70  fof(f44,plain,(
% 2.21/0.70    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.21/0.70    inference(flattening,[],[f43])).
% 2.21/0.70  fof(f43,plain,(
% 2.21/0.70    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.21/0.70    inference(ennf_transformation,[],[f16])).
% 2.21/0.70  fof(f16,axiom,(
% 2.21/0.70    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.21/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 2.21/0.70  fof(f54,plain,(
% 2.21/0.70    v1_funct_2(sK3,sK1,sK0)),
% 2.21/0.70    inference(cnf_transformation,[],[f23])).
% 2.21/0.70  fof(f2785,plain,(
% 2.21/0.70    k2_funct_1(sK3) = k5_relat_1(k6_relat_1(k2_relat_1(sK3)),k2_funct_1(sK3))),
% 2.21/0.70    inference(backward_demodulation,[],[f352,f2784])).
% 2.21/0.70  fof(f2784,plain,(
% 2.21/0.70    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 2.21/0.70    inference(subsumption_resolution,[],[f2783,f53])).
% 2.21/0.70  fof(f2783,plain,(
% 2.21/0.70    ~v1_funct_1(sK3) | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 2.21/0.70    inference(subsumption_resolution,[],[f2760,f299])).
% 2.21/0.70  fof(f299,plain,(
% 2.21/0.70    v1_relat_1(sK3)),
% 2.21/0.70    inference(resolution,[],[f55,f81])).
% 2.21/0.70  fof(f2760,plain,(
% 2.21/0.70    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 2.21/0.70    inference(resolution,[],[f2695,f77])).
% 2.21/0.70  fof(f77,plain,(
% 2.21/0.70    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 2.21/0.70    inference(cnf_transformation,[],[f34])).
% 2.21/0.70  fof(f34,plain,(
% 2.21/0.70    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.21/0.70    inference(flattening,[],[f33])).
% 2.21/0.70  fof(f33,plain,(
% 2.21/0.70    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.21/0.70    inference(ennf_transformation,[],[f7])).
% 2.21/0.70  fof(f7,axiom,(
% 2.21/0.70    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.21/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 2.21/0.70  fof(f2695,plain,(
% 2.21/0.70    v2_funct_1(sK3)),
% 2.21/0.70    inference(subsumption_resolution,[],[f2693,f547])).
% 2.21/0.70  fof(f547,plain,(
% 2.21/0.70    v2_funct_1(k6_relat_1(sK0))),
% 2.21/0.70    inference(subsumption_resolution,[],[f546,f58])).
% 2.21/0.70  fof(f58,plain,(
% 2.21/0.70    v2_funct_1(sK2)),
% 2.21/0.70    inference(cnf_transformation,[],[f23])).
% 2.21/0.70  fof(f546,plain,(
% 2.21/0.70    v2_funct_1(k6_relat_1(sK0)) | ~v2_funct_1(sK2)),
% 2.21/0.70    inference(subsumption_resolution,[],[f545,f62])).
% 2.21/0.70  fof(f545,plain,(
% 2.21/0.70    v2_funct_1(k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2)),
% 2.21/0.70    inference(subsumption_resolution,[],[f540,f378])).
% 2.21/0.70  fof(f540,plain,(
% 2.21/0.70    v2_funct_1(k6_relat_1(sK0)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2)),
% 2.21/0.70    inference(resolution,[],[f539,f73])).
% 2.21/0.70  fof(f73,plain,(
% 2.21/0.70    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | v2_funct_1(k2_funct_1(X0))) )),
% 2.21/0.70    inference(cnf_transformation,[],[f28])).
% 2.21/0.70  fof(f28,plain,(
% 2.21/0.70    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.21/0.70    inference(flattening,[],[f27])).
% 2.21/0.70  fof(f27,plain,(
% 2.21/0.70    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.21/0.70    inference(ennf_transformation,[],[f5])).
% 2.21/0.70  fof(f5,axiom,(
% 2.21/0.70    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.21/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_funct_1)).
% 2.21/0.70  fof(f539,plain,(
% 2.21/0.70    ~v2_funct_1(k2_funct_1(sK2)) | v2_funct_1(k6_relat_1(sK0))),
% 2.21/0.70    inference(subsumption_resolution,[],[f538,f243])).
% 2.21/0.70  fof(f243,plain,(
% 2.21/0.70    v1_funct_1(k2_funct_1(sK2))),
% 2.21/0.70    inference(subsumption_resolution,[],[f242,f56])).
% 2.21/0.70  fof(f242,plain,(
% 2.21/0.70    sK1 != k2_relset_1(sK0,sK1,sK2) | v1_funct_1(k2_funct_1(sK2))),
% 2.21/0.70    inference(subsumption_resolution,[],[f241,f58])).
% 2.21/0.70  fof(f241,plain,(
% 2.21/0.70    ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | v1_funct_1(k2_funct_1(sK2))),
% 2.21/0.70    inference(subsumption_resolution,[],[f240,f64])).
% 2.21/0.70  fof(f240,plain,(
% 2.21/0.70    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | v1_funct_1(k2_funct_1(sK2))),
% 2.21/0.70    inference(subsumption_resolution,[],[f229,f62])).
% 2.21/0.70  fof(f229,plain,(
% 2.21/0.70    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | v1_funct_1(k2_funct_1(sK2))),
% 2.21/0.70    inference(resolution,[],[f63,f83])).
% 2.21/0.70  fof(f83,plain,(
% 2.21/0.70    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2))) )),
% 2.21/0.70    inference(cnf_transformation,[],[f40])).
% 2.21/0.70  fof(f40,plain,(
% 2.21/0.70    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.21/0.70    inference(flattening,[],[f39])).
% 2.21/0.70  fof(f39,plain,(
% 2.21/0.70    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.21/0.70    inference(ennf_transformation,[],[f18])).
% 2.21/0.70  fof(f18,axiom,(
% 2.21/0.70    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.21/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 2.21/0.70  fof(f538,plain,(
% 2.21/0.70    v2_funct_1(k6_relat_1(sK0)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2))),
% 2.21/0.70    inference(subsumption_resolution,[],[f537,f407])).
% 2.21/0.70  fof(f407,plain,(
% 2.21/0.70    v1_relat_1(k2_funct_1(sK2))),
% 2.21/0.70    inference(resolution,[],[f378,f164])).
% 2.21/0.70  fof(f164,plain,(
% 2.21/0.70    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2))),
% 2.21/0.70    inference(resolution,[],[f62,f74])).
% 2.21/0.70  fof(f74,plain,(
% 2.21/0.70    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 2.21/0.70    inference(cnf_transformation,[],[f30])).
% 2.21/0.70  fof(f30,plain,(
% 2.21/0.70    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.21/0.70    inference(flattening,[],[f29])).
% 2.21/0.70  fof(f29,plain,(
% 2.21/0.70    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.21/0.70    inference(ennf_transformation,[],[f4])).
% 2.21/0.70  fof(f4,axiom,(
% 2.21/0.70    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.21/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.21/0.70  fof(f537,plain,(
% 2.21/0.70    v2_funct_1(k6_relat_1(sK0)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2))),
% 2.21/0.70    inference(subsumption_resolution,[],[f536,f58])).
% 2.21/0.70  fof(f536,plain,(
% 2.21/0.70    v2_funct_1(k6_relat_1(sK0)) | ~v2_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2))),
% 2.21/0.70    inference(subsumption_resolution,[],[f535,f62])).
% 2.21/0.70  fof(f535,plain,(
% 2.21/0.70    v2_funct_1(k6_relat_1(sK0)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2))),
% 2.21/0.70    inference(subsumption_resolution,[],[f533,f378])).
% 2.21/0.70  fof(f533,plain,(
% 2.21/0.70    v2_funct_1(k6_relat_1(sK0)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2))),
% 2.21/0.70    inference(superposition,[],[f80,f263])).
% 2.21/0.70  fof(f263,plain,(
% 2.21/0.70    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.21/0.70    inference(subsumption_resolution,[],[f262,f60])).
% 2.21/0.70  fof(f60,plain,(
% 2.21/0.70    k1_xboole_0 != sK1),
% 2.21/0.70    inference(cnf_transformation,[],[f23])).
% 2.21/0.70  fof(f262,plain,(
% 2.21/0.70    k1_xboole_0 = sK1 | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.21/0.70    inference(subsumption_resolution,[],[f261,f58])).
% 2.21/0.70  fof(f261,plain,(
% 2.21/0.70    ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.21/0.70    inference(subsumption_resolution,[],[f260,f56])).
% 2.21/0.70  fof(f260,plain,(
% 2.21/0.70    sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.21/0.70    inference(subsumption_resolution,[],[f259,f64])).
% 2.21/0.70  fof(f259,plain,(
% 2.21/0.70    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.21/0.70    inference(subsumption_resolution,[],[f237,f62])).
% 2.21/0.70  fof(f237,plain,(
% 2.21/0.70    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.21/0.70    inference(resolution,[],[f63,f102])).
% 2.21/0.70  fof(f102,plain,(
% 2.21/0.70    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 2.21/0.70    inference(definition_unfolding,[],[f86,f65])).
% 2.21/0.70  fof(f86,plain,(
% 2.21/0.70    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 2.21/0.70    inference(cnf_transformation,[],[f42])).
% 2.21/0.70  fof(f42,plain,(
% 2.21/0.70    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.21/0.70    inference(flattening,[],[f41])).
% 2.21/0.70  fof(f41,plain,(
% 2.21/0.70    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.21/0.70    inference(ennf_transformation,[],[f19])).
% 2.21/0.70  fof(f19,axiom,(
% 2.21/0.70    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.21/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 2.21/0.70  fof(f80,plain,(
% 2.21/0.70    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | v2_funct_1(k5_relat_1(X0,X1))) )),
% 2.21/0.70    inference(cnf_transformation,[],[f36])).
% 2.21/0.70  fof(f36,plain,(
% 2.21/0.70    ! [X0,X1] : ((v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.21/0.70    inference(flattening,[],[f35])).
% 2.21/0.70  fof(f35,plain,(
% 2.21/0.70    ! [X0,X1] : ((v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.21/0.70    inference(ennf_transformation,[],[f6])).
% 2.21/0.70  fof(f6,axiom,(
% 2.21/0.70    ! [X0,X1] : ((v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 2.21/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc7_funct_1)).
% 2.21/0.70  fof(f2693,plain,(
% 2.21/0.70    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3)),
% 2.21/0.70    inference(backward_demodulation,[],[f2221,f2658])).
% 2.21/0.70  fof(f2221,plain,(
% 2.21/0.70    ~v2_funct_1(k5_relat_1(sK2,sK3)) | v2_funct_1(sK3)),
% 2.21/0.70    inference(forward_demodulation,[],[f2220,f1387])).
% 2.21/0.70  fof(f2220,plain,(
% 2.21/0.70    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | v2_funct_1(sK3)),
% 2.21/0.70    inference(subsumption_resolution,[],[f2219,f59])).
% 2.21/0.70  fof(f59,plain,(
% 2.21/0.70    k1_xboole_0 != sK0),
% 2.21/0.70    inference(cnf_transformation,[],[f23])).
% 2.21/0.70  fof(f2219,plain,(
% 2.21/0.70    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | v2_funct_1(sK3)),
% 2.21/0.70    inference(subsumption_resolution,[],[f2218,f55])).
% 2.21/0.70  fof(f2218,plain,(
% 2.21/0.70    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | v2_funct_1(sK3)),
% 2.21/0.70    inference(subsumption_resolution,[],[f2215,f53])).
% 2.21/0.70  fof(f2215,plain,(
% 2.21/0.70    ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | v2_funct_1(sK3)),
% 2.21/0.70    inference(resolution,[],[f253,f54])).
% 2.21/0.70  fof(f253,plain,(
% 2.21/0.70    ( ! [X4,X5] : (~v1_funct_2(X4,sK1,X5) | ~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,X5))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X5,sK2,X4)) | k1_xboole_0 = X5 | v2_funct_1(X4)) )),
% 2.21/0.70    inference(subsumption_resolution,[],[f252,f56])).
% 2.21/0.70  fof(f252,plain,(
% 2.21/0.70    ( ! [X4,X5] : (~v1_funct_1(X4) | ~v1_funct_2(X4,sK1,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,X5))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X5,sK2,X4)) | sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = X5 | v2_funct_1(X4)) )),
% 2.21/0.70    inference(subsumption_resolution,[],[f251,f64])).
% 2.21/0.70  fof(f251,plain,(
% 2.21/0.70    ( ! [X4,X5] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,sK1,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,X5))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X5,sK2,X4)) | sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = X5 | v2_funct_1(X4)) )),
% 2.21/0.70    inference(subsumption_resolution,[],[f234,f62])).
% 2.21/0.70  fof(f234,plain,(
% 2.21/0.70    ( ! [X4,X5] : (~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,sK1,X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK1,X5))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X5,sK2,X4)) | sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = X5 | v2_funct_1(X4)) )),
% 2.21/0.70    inference(resolution,[],[f63,f92])).
% 2.21/0.70  fof(f92,plain,(
% 2.21/0.70    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4)) )),
% 2.21/0.70    inference(cnf_transformation,[],[f46])).
% 2.21/0.70  fof(f46,plain,(
% 2.21/0.70    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.21/0.70    inference(flattening,[],[f45])).
% 2.21/0.70  fof(f45,plain,(
% 2.21/0.70    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.21/0.70    inference(ennf_transformation,[],[f17])).
% 2.21/0.70  fof(f17,axiom,(
% 2.21/0.70    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.21/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 2.21/0.70  fof(f352,plain,(
% 2.21/0.70    k2_funct_1(sK3) = k5_relat_1(k6_relat_1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3))),
% 2.21/0.70    inference(resolution,[],[f349,f69])).
% 2.21/0.70  fof(f69,plain,(
% 2.21/0.70    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 2.21/0.70    inference(cnf_transformation,[],[f25])).
% 2.21/0.70  fof(f25,plain,(
% 2.21/0.70    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 2.21/0.70    inference(ennf_transformation,[],[f2])).
% 2.21/0.70  fof(f2,axiom,(
% 2.21/0.70    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 2.21/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t78_relat_1)).
% 2.21/0.70  fof(f349,plain,(
% 2.21/0.70    v1_relat_1(k2_funct_1(sK3))),
% 2.21/0.70    inference(resolution,[],[f111,f299])).
% 2.21/0.70  fof(f111,plain,(
% 2.21/0.70    ~v1_relat_1(sK3) | v1_relat_1(k2_funct_1(sK3))),
% 2.21/0.70    inference(resolution,[],[f53,f74])).
% 2.21/0.70  fof(f4765,plain,(
% 2.21/0.70    k5_relat_1(sK2,k6_relat_1(sK1)) = k5_relat_1(k6_relat_1(sK0),k2_funct_1(sK3))),
% 2.21/0.70    inference(forward_demodulation,[],[f4756,f3079])).
% 2.21/0.70  fof(f3079,plain,(
% 2.21/0.70    k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.21/0.70    inference(subsumption_resolution,[],[f3070,f2695])).
% 2.21/0.70  fof(f3070,plain,(
% 2.21/0.70    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.21/0.70    inference(trivial_inequality_removal,[],[f3056])).
% 2.21/0.70  fof(f3056,plain,(
% 2.21/0.70    sK0 != sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.21/0.70    inference(backward_demodulation,[],[f326,f3049])).
% 2.21/0.70  fof(f326,plain,(
% 2.21/0.70    ~v2_funct_1(sK3) | sK0 != k2_relat_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.21/0.70    inference(backward_demodulation,[],[f224,f300])).
% 2.21/0.70  fof(f224,plain,(
% 2.21/0.70    sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.21/0.70    inference(subsumption_resolution,[],[f223,f59])).
% 2.21/0.70  fof(f223,plain,(
% 2.21/0.70    sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.21/0.70    inference(subsumption_resolution,[],[f222,f55])).
% 2.21/0.70  fof(f222,plain,(
% 2.21/0.70    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.21/0.70    inference(subsumption_resolution,[],[f202,f53])).
% 2.21/0.70  fof(f202,plain,(
% 2.21/0.70    ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.21/0.70    inference(resolution,[],[f54,f102])).
% 2.21/0.70  fof(f4756,plain,(
% 2.21/0.70    k5_relat_1(k6_relat_1(sK0),k2_funct_1(sK3)) = k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3)))),
% 2.21/0.70    inference(resolution,[],[f4715,f349])).
% 2.21/0.70  fof(f4715,plain,(
% 2.21/0.70    ( ! [X48] : (~v1_relat_1(X48) | k5_relat_1(sK2,k5_relat_1(sK3,X48)) = k5_relat_1(k6_relat_1(sK0),X48)) )),
% 2.21/0.70    inference(forward_demodulation,[],[f4712,f2658])).
% 2.21/0.70  fof(f4712,plain,(
% 2.21/0.70    ( ! [X48] : (~v1_relat_1(X48) | k5_relat_1(k5_relat_1(sK2,sK3),X48) = k5_relat_1(sK2,k5_relat_1(sK3,X48))) )),
% 2.21/0.70    inference(resolution,[],[f335,f378])).
% 2.21/0.70  fof(f335,plain,(
% 2.21/0.70    ( ! [X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | k5_relat_1(k5_relat_1(X2,sK3),X3) = k5_relat_1(X2,k5_relat_1(sK3,X3))) )),
% 2.21/0.70    inference(resolution,[],[f299,f70])).
% 2.21/0.70  fof(f70,plain,(
% 2.21/0.70    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 2.21/0.70    inference(cnf_transformation,[],[f26])).
% 2.21/0.70  fof(f26,plain,(
% 2.21/0.70    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.21/0.70    inference(ennf_transformation,[],[f1])).
% 2.21/0.70  fof(f1,axiom,(
% 2.21/0.70    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.21/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 2.21/0.70  fof(f2782,plain,(
% 2.21/0.70    sK3 = k2_funct_1(k2_funct_1(sK3))),
% 2.21/0.70    inference(subsumption_resolution,[],[f2781,f53])).
% 2.21/0.70  fof(f2781,plain,(
% 2.21/0.70    ~v1_funct_1(sK3) | sK3 = k2_funct_1(k2_funct_1(sK3))),
% 2.21/0.70    inference(subsumption_resolution,[],[f2759,f299])).
% 2.21/0.70  fof(f2759,plain,(
% 2.21/0.70    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | sK3 = k2_funct_1(k2_funct_1(sK3))),
% 2.21/0.70    inference(resolution,[],[f2695,f76])).
% 2.21/0.70  fof(f76,plain,(
% 2.21/0.70    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0) )),
% 2.21/0.70    inference(cnf_transformation,[],[f32])).
% 2.21/0.70  fof(f32,plain,(
% 2.21/0.70    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.21/0.70    inference(flattening,[],[f31])).
% 2.21/0.70  fof(f31,plain,(
% 2.21/0.70    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.21/0.70    inference(ennf_transformation,[],[f8])).
% 2.21/0.70  fof(f8,axiom,(
% 2.21/0.70    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.21/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_funct_1)).
% 2.21/0.70  % SZS output end Proof for theBenchmark
% 2.21/0.70  % (15171)------------------------------
% 2.21/0.70  % (15171)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.21/0.70  % (15171)Termination reason: Refutation
% 2.21/0.70  
% 2.21/0.70  % (15171)Memory used [KB]: 3198
% 2.21/0.70  % (15171)Time elapsed: 0.289 s
% 2.21/0.70  % (15171)------------------------------
% 2.21/0.70  % (15171)------------------------------
% 2.21/0.71  % (15147)Success in time 0.352 s
%------------------------------------------------------------------------------
