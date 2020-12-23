%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:39 EST 2020

% Result     : Theorem 1.74s
% Output     : Refutation 2.08s
% Verified   : 
% Statistics : Number of formulae       :  158 (2483 expanded)
%              Number of leaves         :   20 ( 447 expanded)
%              Depth                    :   29
%              Number of atoms          :  528 (18804 expanded)
%              Number of equality atoms :  166 (5863 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2020,plain,(
    $false ),
    inference(subsumption_resolution,[],[f2006,f59])).

fof(f59,plain,(
    sK3 != k2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

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
    inference(flattening,[],[f23])).

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
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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

fof(f2006,plain,(
    sK3 = k2_funct_1(sK2) ),
    inference(backward_demodulation,[],[f1534,f1997])).

fof(f1997,plain,(
    sK2 = k4_relat_1(sK3) ),
    inference(forward_demodulation,[],[f1974,f1996])).

fof(f1996,plain,(
    sK2 = k7_relat_1(k4_relat_1(sK3),sK0) ),
    inference(forward_demodulation,[],[f1992,f309])).

fof(f309,plain,(
    sK2 = k5_relat_1(sK2,k6_partfun1(sK1)) ),
    inference(forward_demodulation,[],[f306,f289])).

fof(f289,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f271,f54])).

fof(f54,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f271,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f62,f80])).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f24])).

fof(f306,plain,(
    sK2 = k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2))) ),
    inference(resolution,[],[f270,f95])).

fof(f95,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ) ),
    inference(definition_unfolding,[],[f70,f63])).

fof(f63,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f70,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f270,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f62,f79])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f1992,plain,(
    k5_relat_1(sK2,k6_partfun1(sK1)) = k7_relat_1(k4_relat_1(sK3),sK0) ),
    inference(backward_demodulation,[],[f1531,f1977])).

fof(f1977,plain,(
    k6_partfun1(sK1) = k5_relat_1(sK3,k4_relat_1(sK3)) ),
    inference(trivial_inequality_removal,[],[f1973])).

fof(f1973,plain,
    ( sK0 != sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k4_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f1536,f1966])).

fof(f1966,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f1965,f1275])).

fof(f1275,plain,(
    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f828,f1236])).

fof(f1236,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f1235,f830])).

fof(f830,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(forward_demodulation,[],[f827,f824])).

fof(f824,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f818,f60])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f24])).

fof(f818,plain,
    ( ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f232,f62])).

fof(f232,plain,(
    ! [X12,X10,X11] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ v1_funct_1(X10)
      | k1_partfun1(X11,X12,sK1,sK0,X10,sK3) = k5_relat_1(X10,sK3) ) ),
    inference(subsumption_resolution,[],[f220,f51])).

fof(f51,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f24])).

fof(f220,plain,(
    ! [X12,X10,X11] :
      ( ~ v1_funct_1(X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ v1_funct_1(sK3)
      | k1_partfun1(X11,X12,sK1,sK0,X10,sK3) = k5_relat_1(X10,sK3) ) ),
    inference(resolution,[],[f53,f90])).

fof(f90,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f53,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f827,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(backward_demodulation,[],[f327,f824])).

fof(f327,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(subsumption_resolution,[],[f325,f67])).

fof(f67,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f325,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(resolution,[],[f55,f89])).

fof(f89,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | X2 = X3
      | ~ r2_relset_1(X0,X1,X2,X3) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f55,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f24])).

fof(f1235,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f1234,f53])).

fof(f1234,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1233,f51])).

fof(f1233,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1232,f62])).

fof(f1232,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f1231,f60])).

fof(f1231,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f92,f824])).

fof(f92,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X4)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
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
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f828,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f55,f824])).

fof(f1965,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | sK0 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f1964,f1273])).

fof(f1273,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(backward_demodulation,[],[f824,f1236])).

fof(f1964,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f1963,f62])).

fof(f1963,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f1962,f60])).

fof(f1962,plain,
    ( ~ v1_funct_1(sK2)
    | sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(resolution,[],[f228,f61])).

fof(f61,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f24])).

fof(f228,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,sK0,sK1)
      | ~ v1_funct_1(X0)
      | sK0 = k2_relat_1(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0)) ) ),
    inference(backward_demodulation,[],[f166,f208])).

fof(f208,plain,(
    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f53,f80])).

fof(f166,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0))
      | sK0 = k2_relset_1(sK1,sK0,sK3) ) ),
    inference(subsumption_resolution,[],[f165,f53])).

fof(f165,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0))
      | sK0 = k2_relset_1(sK1,sK0,sK3) ) ),
    inference(subsumption_resolution,[],[f153,f51])).

fof(f153,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0))
      | sK0 = k2_relset_1(sK1,sK0,sK3) ) ),
    inference(resolution,[],[f52,f83])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X3)
      | ~ v1_funct_2(X3,X1,X0)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | k2_relset_1(X0,X1,X2) = X1 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(flattening,[],[f41])).

fof(f41,plain,(
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
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
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

fof(f52,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f24])).

fof(f1536,plain,
    ( sK0 != k2_relat_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k4_relat_1(sK3)) ),
    inference(subsumption_resolution,[],[f1516,f1503])).

fof(f1503,plain,(
    v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1502,f93])).

fof(f93,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f65,f63])).

fof(f65,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f1502,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3) ),
    inference(forward_demodulation,[],[f1501,f1273])).

fof(f1501,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1500,f57])).

fof(f57,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f24])).

fof(f1500,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1499,f53])).

fof(f1499,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f1498,f51])).

fof(f1498,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK3) ),
    inference(resolution,[],[f205,f52])).

fof(f205,plain,(
    ! [X6,X7] :
      ( ~ v1_funct_2(X6,sK1,X7)
      | ~ v1_funct_1(X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6))
      | k1_xboole_0 = X7
      | v2_funct_1(X6) ) ),
    inference(subsumption_resolution,[],[f204,f54])).

fof(f204,plain,(
    ! [X6,X7] :
      ( ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,sK1,X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6))
      | sK1 != k2_relset_1(sK0,sK1,sK2)
      | k1_xboole_0 = X7
      | v2_funct_1(X6) ) ),
    inference(subsumption_resolution,[],[f203,f62])).

fof(f203,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,sK1,X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6))
      | sK1 != k2_relset_1(sK0,sK1,sK2)
      | k1_xboole_0 = X7
      | v2_funct_1(X6) ) ),
    inference(subsumption_resolution,[],[f186,f60])).

fof(f186,plain,(
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
    inference(resolution,[],[f61,f87])).

fof(f87,plain,(
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
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
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

fof(f1516,plain,
    ( k6_partfun1(sK1) = k5_relat_1(sK3,k4_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | sK0 != k2_relat_1(sK3) ),
    inference(backward_demodulation,[],[f230,f1513])).

fof(f1513,plain,(
    k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f1512,f51])).

fof(f1512,plain,
    ( ~ v1_funct_1(sK3)
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f1509,f207])).

fof(f207,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f53,f79])).

fof(f1509,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_funct_1(sK3) = k4_relat_1(sK3) ),
    inference(resolution,[],[f1503,f76])).

fof(f76,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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

fof(f230,plain,
    ( ~ v2_funct_1(sK3)
    | sK0 != k2_relat_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f161,f208])).

fof(f161,plain,
    ( sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f160,f57])).

fof(f160,plain,
    ( sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f159,f53])).

fof(f159,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f151,f51])).

fof(f151,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(resolution,[],[f52,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
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

fof(f1531,plain,(
    k5_relat_1(sK2,k5_relat_1(sK3,k4_relat_1(sK3))) = k7_relat_1(k4_relat_1(sK3),sK0) ),
    inference(backward_demodulation,[],[f1286,f1513])).

fof(f1286,plain,(
    k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) = k7_relat_1(k2_funct_1(sK3),sK0) ),
    inference(forward_demodulation,[],[f1268,f261])).

fof(f261,plain,(
    ! [X6] : k7_relat_1(k2_funct_1(sK3),X6) = k5_relat_1(k6_partfun1(X6),k2_funct_1(sK3)) ),
    inference(resolution,[],[f235,f96])).

fof(f96,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) ) ),
    inference(definition_unfolding,[],[f78,f63])).

fof(f78,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).

fof(f235,plain,(
    v1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f207,f101])).

fof(f101,plain,
    ( ~ v1_relat_1(sK3)
    | v1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f51,f74])).

fof(f74,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
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

fof(f1268,plain,(
    k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f643,f1236])).

fof(f643,plain,(
    k5_relat_1(k5_relat_1(sK2,sK3),k2_funct_1(sK3)) = k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) ),
    inference(resolution,[],[f605,f235])).

fof(f605,plain,(
    ! [X12] :
      ( ~ v1_relat_1(X12)
      | k5_relat_1(k5_relat_1(sK2,sK3),X12) = k5_relat_1(sK2,k5_relat_1(sK3,X12)) ) ),
    inference(resolution,[],[f241,f270])).

fof(f241,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(X2,sK3),X3) = k5_relat_1(X2,k5_relat_1(sK3,X3)) ) ),
    inference(resolution,[],[f207,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
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

fof(f1974,plain,(
    k4_relat_1(sK3) = k7_relat_1(k4_relat_1(sK3),sK0) ),
    inference(backward_demodulation,[],[f1537,f1966])).

fof(f1537,plain,(
    k4_relat_1(sK3) = k7_relat_1(k4_relat_1(sK3),k2_relat_1(sK3)) ),
    inference(forward_demodulation,[],[f1518,f238])).

fof(f238,plain,(
    k2_relat_1(sK3) = k1_relat_1(k4_relat_1(sK3)) ),
    inference(resolution,[],[f207,f71])).

fof(f71,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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

fof(f1518,plain,(
    k4_relat_1(sK3) = k7_relat_1(k4_relat_1(sK3),k1_relat_1(k4_relat_1(sK3))) ),
    inference(backward_demodulation,[],[f250,f1513])).

fof(f250,plain,(
    k2_funct_1(sK3) = k7_relat_1(k2_funct_1(sK3),k1_relat_1(k2_funct_1(sK3))) ),
    inference(resolution,[],[f235,f69])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k7_relat_1(X0,k1_relat_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k7_relat_1(X0,k1_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

fof(f1534,plain,(
    sK3 = k2_funct_1(k4_relat_1(sK3)) ),
    inference(backward_demodulation,[],[f1511,f1513])).

fof(f1511,plain,(
    sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f1510,f51])).

fof(f1510,plain,
    ( ~ v1_funct_1(sK3)
    | sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f1508,f207])).

fof(f1508,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f1503,f77])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 20:50:55 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.52  % (2767)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.21/0.52  % (2745)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.21/0.52  % (2759)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.21/0.52  % (2748)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.21/0.53  % (2752)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.21/0.53  % (2749)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.21/0.53  % (2768)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.21/0.53  % (2769)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.21/0.53  % (2756)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.21/0.53  % (2772)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.21/0.53  % (2750)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.53  % (2755)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.21/0.53  % (2747)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.21/0.54  % (2760)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.21/0.54  % (2763)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.21/0.54  % (2746)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.21/0.54  % (2757)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.21/0.54  % (2761)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.21/0.54  % (2761)Refutation not found, incomplete strategy% (2761)------------------------------
% 0.21/0.54  % (2761)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.54  % (2761)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.54  
% 0.21/0.54  % (2761)Memory used [KB]: 10746
% 0.21/0.54  % (2761)Time elapsed: 0.137 s
% 0.21/0.54  % (2761)------------------------------
% 0.21/0.54  % (2761)------------------------------
% 0.21/0.55  % (2762)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.21/0.55  % (2751)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.55  % (2764)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.21/0.55  % (2770)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.21/0.55  % (2771)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.21/0.55  % (2753)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.21/0.56  % (2773)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.21/0.56  % (2754)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 1.56/0.57  % (2765)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 1.56/0.58  % (2758)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 1.74/0.59  % (2766)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 1.74/0.60  % (2774)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 1.74/0.63  % (2762)Refutation found. Thanks to Tanya!
% 1.74/0.63  % SZS status Theorem for theBenchmark
% 2.08/0.65  % SZS output start Proof for theBenchmark
% 2.08/0.65  fof(f2020,plain,(
% 2.08/0.65    $false),
% 2.08/0.65    inference(subsumption_resolution,[],[f2006,f59])).
% 2.08/0.65  fof(f59,plain,(
% 2.08/0.65    sK3 != k2_funct_1(sK2)),
% 2.08/0.65    inference(cnf_transformation,[],[f24])).
% 2.08/0.65  fof(f24,plain,(
% 2.08/0.65    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.08/0.65    inference(flattening,[],[f23])).
% 2.08/0.65  fof(f23,plain,(
% 2.08/0.65    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.08/0.65    inference(ennf_transformation,[],[f22])).
% 2.08/0.65  fof(f22,negated_conjecture,(
% 2.08/0.65    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.08/0.65    inference(negated_conjecture,[],[f21])).
% 2.08/0.65  fof(f21,conjecture,(
% 2.08/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.08/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 2.08/0.65  fof(f2006,plain,(
% 2.08/0.65    sK3 = k2_funct_1(sK2)),
% 2.08/0.65    inference(backward_demodulation,[],[f1534,f1997])).
% 2.08/0.65  fof(f1997,plain,(
% 2.08/0.65    sK2 = k4_relat_1(sK3)),
% 2.08/0.65    inference(forward_demodulation,[],[f1974,f1996])).
% 2.08/0.65  fof(f1996,plain,(
% 2.08/0.65    sK2 = k7_relat_1(k4_relat_1(sK3),sK0)),
% 2.08/0.65    inference(forward_demodulation,[],[f1992,f309])).
% 2.08/0.65  fof(f309,plain,(
% 2.08/0.65    sK2 = k5_relat_1(sK2,k6_partfun1(sK1))),
% 2.08/0.65    inference(forward_demodulation,[],[f306,f289])).
% 2.08/0.65  fof(f289,plain,(
% 2.08/0.65    sK1 = k2_relat_1(sK2)),
% 2.08/0.65    inference(forward_demodulation,[],[f271,f54])).
% 2.08/0.65  fof(f54,plain,(
% 2.08/0.65    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.08/0.65    inference(cnf_transformation,[],[f24])).
% 2.08/0.65  fof(f271,plain,(
% 2.08/0.65    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 2.08/0.65    inference(resolution,[],[f62,f80])).
% 2.08/0.65  fof(f80,plain,(
% 2.08/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 2.08/0.65    inference(cnf_transformation,[],[f38])).
% 2.08/0.65  fof(f38,plain,(
% 2.08/0.65    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.08/0.65    inference(ennf_transformation,[],[f12])).
% 2.08/0.65  fof(f12,axiom,(
% 2.08/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.08/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.08/0.65  fof(f62,plain,(
% 2.08/0.65    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.08/0.65    inference(cnf_transformation,[],[f24])).
% 2.08/0.65  fof(f306,plain,(
% 2.08/0.65    sK2 = k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2)))),
% 2.08/0.65    inference(resolution,[],[f270,f95])).
% 2.08/0.65  fof(f95,plain,(
% 2.08/0.65    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0) )),
% 2.08/0.65    inference(definition_unfolding,[],[f70,f63])).
% 2.08/0.65  fof(f63,plain,(
% 2.08/0.65    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.08/0.65    inference(cnf_transformation,[],[f17])).
% 2.08/0.65  fof(f17,axiom,(
% 2.08/0.65    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.08/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.08/0.65  fof(f70,plain,(
% 2.08/0.65    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 2.08/0.65    inference(cnf_transformation,[],[f27])).
% 2.08/0.65  fof(f27,plain,(
% 2.08/0.65    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 2.08/0.65    inference(ennf_transformation,[],[f4])).
% 2.08/0.65  fof(f4,axiom,(
% 2.08/0.65    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 2.08/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 2.08/0.65  fof(f270,plain,(
% 2.08/0.65    v1_relat_1(sK2)),
% 2.08/0.65    inference(resolution,[],[f62,f79])).
% 2.08/0.65  fof(f79,plain,(
% 2.08/0.65    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.08/0.65    inference(cnf_transformation,[],[f37])).
% 2.08/0.65  fof(f37,plain,(
% 2.08/0.65    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.08/0.65    inference(ennf_transformation,[],[f11])).
% 2.08/0.65  fof(f11,axiom,(
% 2.08/0.65    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.08/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.08/0.65  fof(f1992,plain,(
% 2.08/0.65    k5_relat_1(sK2,k6_partfun1(sK1)) = k7_relat_1(k4_relat_1(sK3),sK0)),
% 2.08/0.65    inference(backward_demodulation,[],[f1531,f1977])).
% 2.08/0.65  fof(f1977,plain,(
% 2.08/0.65    k6_partfun1(sK1) = k5_relat_1(sK3,k4_relat_1(sK3))),
% 2.08/0.65    inference(trivial_inequality_removal,[],[f1973])).
% 2.08/0.65  fof(f1973,plain,(
% 2.08/0.65    sK0 != sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k4_relat_1(sK3))),
% 2.08/0.65    inference(backward_demodulation,[],[f1536,f1966])).
% 2.08/0.65  fof(f1966,plain,(
% 2.08/0.65    sK0 = k2_relat_1(sK3)),
% 2.08/0.65    inference(subsumption_resolution,[],[f1965,f1275])).
% 2.08/0.65  fof(f1275,plain,(
% 2.08/0.65    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))),
% 2.08/0.65    inference(backward_demodulation,[],[f828,f1236])).
% 2.08/0.65  fof(f1236,plain,(
% 2.08/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.08/0.65    inference(resolution,[],[f1235,f830])).
% 2.08/0.65  fof(f830,plain,(
% 2.08/0.65    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.08/0.65    inference(forward_demodulation,[],[f827,f824])).
% 2.08/0.65  fof(f824,plain,(
% 2.08/0.65    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.08/0.65    inference(subsumption_resolution,[],[f818,f60])).
% 2.08/0.65  fof(f60,plain,(
% 2.08/0.65    v1_funct_1(sK2)),
% 2.08/0.65    inference(cnf_transformation,[],[f24])).
% 2.08/0.65  fof(f818,plain,(
% 2.08/0.65    ~v1_funct_1(sK2) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.08/0.65    inference(resolution,[],[f232,f62])).
% 2.08/0.65  fof(f232,plain,(
% 2.08/0.65    ( ! [X12,X10,X11] : (~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) | ~v1_funct_1(X10) | k1_partfun1(X11,X12,sK1,sK0,X10,sK3) = k5_relat_1(X10,sK3)) )),
% 2.08/0.65    inference(subsumption_resolution,[],[f220,f51])).
% 2.08/0.65  fof(f51,plain,(
% 2.08/0.65    v1_funct_1(sK3)),
% 2.08/0.65    inference(cnf_transformation,[],[f24])).
% 2.08/0.65  fof(f220,plain,(
% 2.08/0.65    ( ! [X12,X10,X11] : (~v1_funct_1(X10) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) | ~v1_funct_1(sK3) | k1_partfun1(X11,X12,sK1,sK0,X10,sK3) = k5_relat_1(X10,sK3)) )),
% 2.08/0.65    inference(resolution,[],[f53,f90])).
% 2.08/0.65  fof(f90,plain,(
% 2.08/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 2.08/0.65    inference(cnf_transformation,[],[f48])).
% 2.08/0.65  fof(f48,plain,(
% 2.08/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.08/0.65    inference(flattening,[],[f47])).
% 2.08/0.65  fof(f47,plain,(
% 2.08/0.65    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.08/0.65    inference(ennf_transformation,[],[f16])).
% 2.08/0.65  fof(f16,axiom,(
% 2.08/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.08/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.08/0.65  fof(f53,plain,(
% 2.08/0.65    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.08/0.65    inference(cnf_transformation,[],[f24])).
% 2.08/0.65  fof(f827,plain,(
% 2.08/0.65    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.08/0.65    inference(backward_demodulation,[],[f327,f824])).
% 2.08/0.65  fof(f327,plain,(
% 2.08/0.65    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.08/0.65    inference(subsumption_resolution,[],[f325,f67])).
% 2.08/0.65  fof(f67,plain,(
% 2.08/0.65    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.08/0.65    inference(cnf_transformation,[],[f15])).
% 2.08/0.65  fof(f15,axiom,(
% 2.08/0.65    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 2.08/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 2.08/0.65  fof(f325,plain,(
% 2.08/0.65    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.08/0.65    inference(resolution,[],[f55,f89])).
% 2.08/0.65  fof(f89,plain,(
% 2.08/0.65    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 2.08/0.65    inference(cnf_transformation,[],[f46])).
% 2.08/0.65  fof(f46,plain,(
% 2.08/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.08/0.65    inference(flattening,[],[f45])).
% 2.08/0.65  fof(f45,plain,(
% 2.08/0.65    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.08/0.65    inference(ennf_transformation,[],[f13])).
% 2.08/0.65  fof(f13,axiom,(
% 2.08/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.08/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.08/0.65  fof(f55,plain,(
% 2.08/0.65    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.08/0.65    inference(cnf_transformation,[],[f24])).
% 2.08/0.65  fof(f1235,plain,(
% 2.08/0.65    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.08/0.65    inference(subsumption_resolution,[],[f1234,f53])).
% 2.08/0.65  fof(f1234,plain,(
% 2.08/0.65    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.08/0.65    inference(subsumption_resolution,[],[f1233,f51])).
% 2.08/0.65  fof(f1233,plain,(
% 2.08/0.65    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.08/0.65    inference(subsumption_resolution,[],[f1232,f62])).
% 2.08/0.65  fof(f1232,plain,(
% 2.08/0.65    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.08/0.65    inference(subsumption_resolution,[],[f1231,f60])).
% 2.08/0.65  fof(f1231,plain,(
% 2.08/0.65    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.08/0.65    inference(superposition,[],[f92,f824])).
% 2.08/0.65  fof(f92,plain,(
% 2.08/0.65    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))) )),
% 2.08/0.65    inference(cnf_transformation,[],[f50])).
% 2.08/0.65  fof(f50,plain,(
% 2.08/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.08/0.65    inference(flattening,[],[f49])).
% 2.08/0.65  fof(f49,plain,(
% 2.08/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.08/0.65    inference(ennf_transformation,[],[f14])).
% 2.08/0.65  fof(f14,axiom,(
% 2.08/0.65    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.08/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.08/0.65  fof(f828,plain,(
% 2.08/0.65    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 2.08/0.65    inference(backward_demodulation,[],[f55,f824])).
% 2.08/0.65  fof(f1965,plain,(
% 2.08/0.65    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | sK0 = k2_relat_1(sK3)),
% 2.08/0.65    inference(forward_demodulation,[],[f1964,f1273])).
% 2.08/0.65  fof(f1273,plain,(
% 2.08/0.65    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.08/0.65    inference(backward_demodulation,[],[f824,f1236])).
% 2.08/0.65  fof(f1964,plain,(
% 2.08/0.65    sK0 = k2_relat_1(sK3) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.08/0.65    inference(subsumption_resolution,[],[f1963,f62])).
% 2.08/0.65  fof(f1963,plain,(
% 2.08/0.65    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.08/0.65    inference(subsumption_resolution,[],[f1962,f60])).
% 2.08/0.65  fof(f1962,plain,(
% 2.08/0.65    ~v1_funct_1(sK2) | sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.08/0.65    inference(resolution,[],[f228,f61])).
% 2.08/0.65  fof(f61,plain,(
% 2.08/0.65    v1_funct_2(sK2,sK0,sK1)),
% 2.08/0.65    inference(cnf_transformation,[],[f24])).
% 2.08/0.65  fof(f228,plain,(
% 2.08/0.65    ( ! [X0] : (~v1_funct_2(X0,sK0,sK1) | ~v1_funct_1(X0) | sK0 = k2_relat_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0))) )),
% 2.08/0.65    inference(backward_demodulation,[],[f166,f208])).
% 2.08/0.65  fof(f208,plain,(
% 2.08/0.65    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)),
% 2.08/0.65    inference(resolution,[],[f53,f80])).
% 2.08/0.65  fof(f166,plain,(
% 2.08/0.65    ( ! [X0] : (~v1_funct_1(X0) | ~v1_funct_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3)) )),
% 2.08/0.65    inference(subsumption_resolution,[],[f165,f53])).
% 2.08/0.65  fof(f165,plain,(
% 2.08/0.65    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3)) )),
% 2.08/0.65    inference(subsumption_resolution,[],[f153,f51])).
% 2.08/0.65  fof(f153,plain,(
% 2.08/0.65    ( ! [X0] : (~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3)) )),
% 2.08/0.65    inference(resolution,[],[f52,f83])).
% 2.08/0.65  fof(f83,plain,(
% 2.08/0.65    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1) )),
% 2.08/0.65    inference(cnf_transformation,[],[f42])).
% 2.08/0.65  fof(f42,plain,(
% 2.08/0.65    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.08/0.65    inference(flattening,[],[f41])).
% 2.08/0.65  fof(f41,plain,(
% 2.08/0.65    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.08/0.65    inference(ennf_transformation,[],[f18])).
% 2.08/0.65  fof(f18,axiom,(
% 2.08/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.08/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 2.08/0.65  fof(f52,plain,(
% 2.08/0.65    v1_funct_2(sK3,sK1,sK0)),
% 2.08/0.65    inference(cnf_transformation,[],[f24])).
% 2.08/0.65  fof(f1536,plain,(
% 2.08/0.65    sK0 != k2_relat_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k4_relat_1(sK3))),
% 2.08/0.65    inference(subsumption_resolution,[],[f1516,f1503])).
% 2.08/0.65  fof(f1503,plain,(
% 2.08/0.65    v2_funct_1(sK3)),
% 2.08/0.65    inference(subsumption_resolution,[],[f1502,f93])).
% 2.08/0.65  fof(f93,plain,(
% 2.08/0.65    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 2.08/0.65    inference(definition_unfolding,[],[f65,f63])).
% 2.08/0.65  fof(f65,plain,(
% 2.08/0.65    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 2.08/0.65    inference(cnf_transformation,[],[f9])).
% 2.08/0.65  fof(f9,axiom,(
% 2.08/0.65    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 2.08/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 2.08/0.65  fof(f1502,plain,(
% 2.08/0.65    ~v2_funct_1(k6_partfun1(sK0)) | v2_funct_1(sK3)),
% 2.08/0.65    inference(forward_demodulation,[],[f1501,f1273])).
% 2.08/0.65  fof(f1501,plain,(
% 2.08/0.65    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | v2_funct_1(sK3)),
% 2.08/0.65    inference(subsumption_resolution,[],[f1500,f57])).
% 2.08/0.65  fof(f57,plain,(
% 2.08/0.65    k1_xboole_0 != sK0),
% 2.08/0.65    inference(cnf_transformation,[],[f24])).
% 2.08/0.65  fof(f1500,plain,(
% 2.08/0.65    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | v2_funct_1(sK3)),
% 2.08/0.65    inference(subsumption_resolution,[],[f1499,f53])).
% 2.08/0.65  fof(f1499,plain,(
% 2.08/0.65    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | v2_funct_1(sK3)),
% 2.08/0.65    inference(subsumption_resolution,[],[f1498,f51])).
% 2.08/0.65  fof(f1498,plain,(
% 2.08/0.65    ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | v2_funct_1(sK3)),
% 2.08/0.65    inference(resolution,[],[f205,f52])).
% 2.08/0.65  fof(f205,plain,(
% 2.08/0.65    ( ! [X6,X7] : (~v1_funct_2(X6,sK1,X7) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6)) | k1_xboole_0 = X7 | v2_funct_1(X6)) )),
% 2.08/0.65    inference(subsumption_resolution,[],[f204,f54])).
% 2.08/0.65  fof(f204,plain,(
% 2.08/0.65    ( ! [X6,X7] : (~v1_funct_1(X6) | ~v1_funct_2(X6,sK1,X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6)) | sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = X7 | v2_funct_1(X6)) )),
% 2.08/0.65    inference(subsumption_resolution,[],[f203,f62])).
% 2.08/0.65  fof(f203,plain,(
% 2.08/0.65    ( ! [X6,X7] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X6) | ~v1_funct_2(X6,sK1,X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6)) | sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = X7 | v2_funct_1(X6)) )),
% 2.08/0.65    inference(subsumption_resolution,[],[f186,f60])).
% 2.08/0.65  fof(f186,plain,(
% 2.08/0.65    ( ! [X6,X7] : (~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X6) | ~v1_funct_2(X6,sK1,X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6)) | sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = X7 | v2_funct_1(X6)) )),
% 2.08/0.65    inference(resolution,[],[f61,f87])).
% 2.08/0.65  fof(f87,plain,(
% 2.08/0.65    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4)) )),
% 2.08/0.65    inference(cnf_transformation,[],[f44])).
% 2.08/0.65  fof(f44,plain,(
% 2.08/0.65    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.08/0.65    inference(flattening,[],[f43])).
% 2.08/0.65  fof(f43,plain,(
% 2.08/0.65    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.08/0.65    inference(ennf_transformation,[],[f19])).
% 2.08/0.65  fof(f19,axiom,(
% 2.08/0.65    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.08/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 2.08/0.65  fof(f1516,plain,(
% 2.08/0.65    k6_partfun1(sK1) = k5_relat_1(sK3,k4_relat_1(sK3)) | ~v2_funct_1(sK3) | sK0 != k2_relat_1(sK3)),
% 2.08/0.65    inference(backward_demodulation,[],[f230,f1513])).
% 2.08/0.65  fof(f1513,plain,(
% 2.08/0.65    k2_funct_1(sK3) = k4_relat_1(sK3)),
% 2.08/0.65    inference(subsumption_resolution,[],[f1512,f51])).
% 2.08/0.65  fof(f1512,plain,(
% 2.08/0.65    ~v1_funct_1(sK3) | k2_funct_1(sK3) = k4_relat_1(sK3)),
% 2.08/0.65    inference(subsumption_resolution,[],[f1509,f207])).
% 2.08/0.65  fof(f207,plain,(
% 2.08/0.65    v1_relat_1(sK3)),
% 2.08/0.65    inference(resolution,[],[f53,f79])).
% 2.08/0.65  fof(f1509,plain,(
% 2.08/0.65    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | k2_funct_1(sK3) = k4_relat_1(sK3)),
% 2.08/0.65    inference(resolution,[],[f1503,f76])).
% 2.08/0.65  fof(f76,plain,(
% 2.08/0.65    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0)) )),
% 2.08/0.65    inference(cnf_transformation,[],[f33])).
% 2.08/0.65  fof(f33,plain,(
% 2.08/0.65    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.08/0.65    inference(flattening,[],[f32])).
% 2.08/0.65  fof(f32,plain,(
% 2.08/0.65    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.08/0.65    inference(ennf_transformation,[],[f7])).
% 2.08/0.65  fof(f7,axiom,(
% 2.08/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.08/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 2.08/0.65  fof(f230,plain,(
% 2.08/0.65    ~v2_funct_1(sK3) | sK0 != k2_relat_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.08/0.65    inference(backward_demodulation,[],[f161,f208])).
% 2.08/0.65  fof(f161,plain,(
% 2.08/0.65    sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.08/0.65    inference(subsumption_resolution,[],[f160,f57])).
% 2.08/0.65  fof(f160,plain,(
% 2.08/0.65    sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.08/0.65    inference(subsumption_resolution,[],[f159,f53])).
% 2.08/0.65  fof(f159,plain,(
% 2.08/0.65    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.08/0.65    inference(subsumption_resolution,[],[f151,f51])).
% 2.08/0.65  fof(f151,plain,(
% 2.08/0.65    ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.08/0.65    inference(resolution,[],[f52,f81])).
% 2.08/0.65  fof(f81,plain,(
% 2.08/0.65    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 2.08/0.65    inference(cnf_transformation,[],[f40])).
% 2.08/0.65  fof(f40,plain,(
% 2.08/0.65    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.08/0.65    inference(flattening,[],[f39])).
% 2.08/0.65  fof(f39,plain,(
% 2.08/0.65    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.08/0.65    inference(ennf_transformation,[],[f20])).
% 2.08/0.65  fof(f20,axiom,(
% 2.08/0.65    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.08/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 2.08/0.65  fof(f1531,plain,(
% 2.08/0.65    k5_relat_1(sK2,k5_relat_1(sK3,k4_relat_1(sK3))) = k7_relat_1(k4_relat_1(sK3),sK0)),
% 2.08/0.65    inference(backward_demodulation,[],[f1286,f1513])).
% 2.08/0.65  fof(f1286,plain,(
% 2.08/0.65    k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) = k7_relat_1(k2_funct_1(sK3),sK0)),
% 2.08/0.65    inference(forward_demodulation,[],[f1268,f261])).
% 2.08/0.65  fof(f261,plain,(
% 2.08/0.65    ( ! [X6] : (k7_relat_1(k2_funct_1(sK3),X6) = k5_relat_1(k6_partfun1(X6),k2_funct_1(sK3))) )),
% 2.08/0.65    inference(resolution,[],[f235,f96])).
% 2.08/0.65  fof(f96,plain,(
% 2.08/0.65    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)) )),
% 2.08/0.65    inference(definition_unfolding,[],[f78,f63])).
% 2.08/0.65  fof(f78,plain,(
% 2.08/0.65    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)) )),
% 2.08/0.65    inference(cnf_transformation,[],[f36])).
% 2.08/0.65  fof(f36,plain,(
% 2.08/0.65    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.08/0.65    inference(ennf_transformation,[],[f5])).
% 2.08/0.65  fof(f5,axiom,(
% 2.08/0.65    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.08/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_relat_1)).
% 2.08/0.65  fof(f235,plain,(
% 2.08/0.65    v1_relat_1(k2_funct_1(sK3))),
% 2.08/0.65    inference(resolution,[],[f207,f101])).
% 2.08/0.65  fof(f101,plain,(
% 2.08/0.65    ~v1_relat_1(sK3) | v1_relat_1(k2_funct_1(sK3))),
% 2.08/0.65    inference(resolution,[],[f51,f74])).
% 2.08/0.65  fof(f74,plain,(
% 2.08/0.65    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 2.08/0.65    inference(cnf_transformation,[],[f31])).
% 2.08/0.65  fof(f31,plain,(
% 2.08/0.65    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.08/0.65    inference(flattening,[],[f30])).
% 2.08/0.65  fof(f30,plain,(
% 2.08/0.65    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.08/0.65    inference(ennf_transformation,[],[f8])).
% 2.08/0.65  fof(f8,axiom,(
% 2.08/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.08/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.08/0.65  fof(f1268,plain,(
% 2.08/0.65    k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))),
% 2.08/0.65    inference(backward_demodulation,[],[f643,f1236])).
% 2.08/0.65  fof(f643,plain,(
% 2.08/0.65    k5_relat_1(k5_relat_1(sK2,sK3),k2_funct_1(sK3)) = k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3)))),
% 2.08/0.65    inference(resolution,[],[f605,f235])).
% 2.08/0.65  fof(f605,plain,(
% 2.08/0.65    ( ! [X12] : (~v1_relat_1(X12) | k5_relat_1(k5_relat_1(sK2,sK3),X12) = k5_relat_1(sK2,k5_relat_1(sK3,X12))) )),
% 2.08/0.65    inference(resolution,[],[f241,f270])).
% 2.08/0.65  fof(f241,plain,(
% 2.08/0.65    ( ! [X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | k5_relat_1(k5_relat_1(X2,sK3),X3) = k5_relat_1(X2,k5_relat_1(sK3,X3))) )),
% 2.08/0.65    inference(resolution,[],[f207,f73])).
% 2.08/0.65  fof(f73,plain,(
% 2.08/0.65    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 2.08/0.65    inference(cnf_transformation,[],[f29])).
% 2.08/0.65  fof(f29,plain,(
% 2.08/0.65    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.08/0.65    inference(ennf_transformation,[],[f3])).
% 2.08/0.65  fof(f3,axiom,(
% 2.08/0.65    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.08/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 2.08/0.65  fof(f1974,plain,(
% 2.08/0.65    k4_relat_1(sK3) = k7_relat_1(k4_relat_1(sK3),sK0)),
% 2.08/0.65    inference(backward_demodulation,[],[f1537,f1966])).
% 2.08/0.65  fof(f1537,plain,(
% 2.08/0.65    k4_relat_1(sK3) = k7_relat_1(k4_relat_1(sK3),k2_relat_1(sK3))),
% 2.08/0.65    inference(forward_demodulation,[],[f1518,f238])).
% 2.08/0.65  fof(f238,plain,(
% 2.08/0.65    k2_relat_1(sK3) = k1_relat_1(k4_relat_1(sK3))),
% 2.08/0.65    inference(resolution,[],[f207,f71])).
% 2.08/0.65  fof(f71,plain,(
% 2.08/0.65    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 2.08/0.65    inference(cnf_transformation,[],[f28])).
% 2.08/0.65  fof(f28,plain,(
% 2.08/0.65    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 2.08/0.65    inference(ennf_transformation,[],[f2])).
% 2.08/0.65  fof(f2,axiom,(
% 2.08/0.65    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 2.08/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t37_relat_1)).
% 2.08/0.65  fof(f1518,plain,(
% 2.08/0.65    k4_relat_1(sK3) = k7_relat_1(k4_relat_1(sK3),k1_relat_1(k4_relat_1(sK3)))),
% 2.08/0.65    inference(backward_demodulation,[],[f250,f1513])).
% 2.08/0.65  fof(f250,plain,(
% 2.08/0.65    k2_funct_1(sK3) = k7_relat_1(k2_funct_1(sK3),k1_relat_1(k2_funct_1(sK3)))),
% 2.08/0.65    inference(resolution,[],[f235,f69])).
% 2.08/0.65  fof(f69,plain,(
% 2.08/0.65    ( ! [X0] : (~v1_relat_1(X0) | k7_relat_1(X0,k1_relat_1(X0)) = X0) )),
% 2.08/0.65    inference(cnf_transformation,[],[f26])).
% 2.08/0.65  fof(f26,plain,(
% 2.08/0.65    ! [X0] : (k7_relat_1(X0,k1_relat_1(X0)) = X0 | ~v1_relat_1(X0))),
% 2.08/0.65    inference(ennf_transformation,[],[f6])).
% 2.08/0.65  fof(f6,axiom,(
% 2.08/0.65    ! [X0] : (v1_relat_1(X0) => k7_relat_1(X0,k1_relat_1(X0)) = X0)),
% 2.08/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).
% 2.08/0.65  fof(f1534,plain,(
% 2.08/0.65    sK3 = k2_funct_1(k4_relat_1(sK3))),
% 2.08/0.65    inference(backward_demodulation,[],[f1511,f1513])).
% 2.08/0.65  fof(f1511,plain,(
% 2.08/0.65    sK3 = k2_funct_1(k2_funct_1(sK3))),
% 2.08/0.65    inference(subsumption_resolution,[],[f1510,f51])).
% 2.08/0.65  fof(f1510,plain,(
% 2.08/0.65    ~v1_funct_1(sK3) | sK3 = k2_funct_1(k2_funct_1(sK3))),
% 2.08/0.65    inference(subsumption_resolution,[],[f1508,f207])).
% 2.08/0.65  fof(f1508,plain,(
% 2.08/0.65    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | sK3 = k2_funct_1(k2_funct_1(sK3))),
% 2.08/0.65    inference(resolution,[],[f1503,f77])).
% 2.08/0.65  fof(f77,plain,(
% 2.08/0.65    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0) )),
% 2.08/0.65    inference(cnf_transformation,[],[f35])).
% 2.08/0.65  fof(f35,plain,(
% 2.08/0.65    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.08/0.65    inference(flattening,[],[f34])).
% 2.08/0.65  fof(f34,plain,(
% 2.08/0.65    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.08/0.65    inference(ennf_transformation,[],[f10])).
% 2.08/0.65  fof(f10,axiom,(
% 2.08/0.65    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.08/0.65    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 2.08/0.65  % SZS output end Proof for theBenchmark
% 2.08/0.65  % (2762)------------------------------
% 2.08/0.65  % (2762)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.08/0.65  % (2762)Termination reason: Refutation
% 2.08/0.65  
% 2.08/0.65  % (2762)Memory used [KB]: 2686
% 2.08/0.65  % (2762)Time elapsed: 0.225 s
% 2.08/0.65  % (2762)------------------------------
% 2.08/0.65  % (2762)------------------------------
% 2.08/0.66  % (2743)Success in time 0.292 s
%------------------------------------------------------------------------------
