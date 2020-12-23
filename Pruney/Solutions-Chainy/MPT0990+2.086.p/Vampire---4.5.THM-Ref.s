%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:43 EST 2020

% Result     : Theorem 2.59s
% Output     : Refutation 2.59s
% Verified   : 
% Statistics : Number of formulae       :  181 (2186 expanded)
%              Number of leaves         :   20 ( 393 expanded)
%              Depth                    :   30
%              Number of atoms          :  669 (16574 expanded)
%              Number of equality atoms :  175 (5130 expanded)
%              Maximal formula depth    :   15 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f4862,plain,(
    $false ),
    inference(subsumption_resolution,[],[f4767,f61])).

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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).

fof(f4767,plain,(
    sK3 = k2_funct_1(sK2) ),
    inference(backward_demodulation,[],[f2778,f4761])).

fof(f4761,plain,(
    sK2 = k2_funct_1(sK3) ),
    inference(forward_demodulation,[],[f4760,f421])).

fof(f421,plain,(
    sK2 = k5_relat_1(sK2,k6_partfun1(sK1)) ),
    inference(forward_demodulation,[],[f419,f396])).

fof(f396,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f375,f56])).

fof(f56,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f375,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f64,f81])).

fof(f81,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f64,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f23])).

fof(f419,plain,(
    sK2 = k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2))) ),
    inference(resolution,[],[f374,f98])).

fof(f98,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ) ),
    inference(definition_unfolding,[],[f67,f65])).

fof(f65,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f67,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).

fof(f374,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f64,f80])).

fof(f80,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f4760,plain,(
    k2_funct_1(sK3) = k5_relat_1(sK2,k6_partfun1(sK1)) ),
    inference(forward_demodulation,[],[f4759,f3060])).

fof(f3060,plain,(
    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f2781,f3045])).

fof(f3045,plain,(
    sK0 = k2_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f3044,f2687])).

fof(f2687,plain,(
    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f1387,f2654])).

fof(f2654,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f2645,f1389])).

fof(f1389,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(forward_demodulation,[],[f1386,f1383])).

fof(f1383,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f1374,f62])).

fof(f62,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f1374,plain,
    ( ~ v1_funct_1(sK2)
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(resolution,[],[f325,f64])).

fof(f325,plain,(
    ! [X12,X10,X11] :
      ( ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ v1_funct_1(X10)
      | k1_partfun1(X11,X12,sK1,sK0,X10,sK3) = k5_relat_1(X10,sK3) ) ),
    inference(subsumption_resolution,[],[f311,f53])).

fof(f53,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f23])).

fof(f311,plain,(
    ! [X12,X10,X11] :
      ( ~ v1_funct_1(X10)
      | ~ m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12)))
      | ~ v1_funct_1(sK3)
      | k1_partfun1(X11,X12,sK1,sK0,X10,sK3) = k5_relat_1(X10,sK3) ) ),
    inference(resolution,[],[f55,f94])).

fof(f94,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f23])).

fof(f1386,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(backward_demodulation,[],[f425,f1383])).

fof(f425,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(subsumption_resolution,[],[f423,f97])).

fof(f97,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f66,f65])).

fof(f66,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).

fof(f423,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(resolution,[],[f57,f93])).

fof(f93,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f57,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f23])).

fof(f2645,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f2644,f55])).

fof(f2644,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f2643,f53])).

fof(f2643,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f2642,f64])).

fof(f2642,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(subsumption_resolution,[],[f2641,f62])).

fof(f2641,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(superposition,[],[f96,f1383])).

fof(f96,plain,(
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

fof(f1387,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f57,f1383])).

fof(f3044,plain,
    ( ~ r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))
    | sK0 = k2_relat_1(sK3) ),
    inference(forward_demodulation,[],[f3043,f2685])).

fof(f2685,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0) ),
    inference(backward_demodulation,[],[f1383,f2654])).

fof(f3043,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f3042,f64])).

fof(f3042,plain,
    ( sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f3039,f62])).

fof(f3039,plain,
    ( ~ v1_funct_1(sK2)
    | sK0 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(resolution,[],[f321,f63])).

fof(f63,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f23])).

fof(f321,plain,(
    ! [X0] :
      ( ~ v1_funct_2(X0,sK0,sK1)
      | ~ v1_funct_1(X0)
      | sK0 = k2_relat_1(sK3)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0)) ) ),
    inference(backward_demodulation,[],[f212,f296])).

fof(f296,plain,(
    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3) ),
    inference(resolution,[],[f55,f81])).

fof(f212,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0))
      | sK0 = k2_relset_1(sK1,sK0,sK3) ) ),
    inference(subsumption_resolution,[],[f211,f55])).

fof(f211,plain,(
    ! [X0] :
      ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0))
      | sK0 = k2_relset_1(sK1,sK0,sK3) ) ),
    inference(subsumption_resolution,[],[f195,f53])).

fof(f195,plain,(
    ! [X0] :
      ( ~ v1_funct_1(sK3)
      | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,sK0,sK1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0))
      | sK0 = k2_relset_1(sK1,sK0,sK3) ) ),
    inference(resolution,[],[f54,f87])).

fof(f87,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).

fof(f54,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f23])).

fof(f2781,plain,(
    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(k2_relat_1(sK3)),k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f363,f2780])).

fof(f2780,plain,(
    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f2779,f53])).

fof(f2779,plain,
    ( ~ v1_funct_1(sK3)
    | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f2756,f295])).

fof(f295,plain,(
    v1_relat_1(sK3) ),
    inference(resolution,[],[f55,f80])).

fof(f2756,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f2691,f76])).

fof(f76,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f2691,plain,(
    v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f2689,f510])).

fof(f510,plain,(
    v2_funct_1(k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f509,f58])).

fof(f58,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f23])).

fof(f509,plain,
    ( v2_funct_1(k6_partfun1(sK0))
    | ~ v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f508,f62])).

fof(f508,plain,
    ( v2_funct_1(k6_partfun1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f503,f374])).

fof(f503,plain,
    ( v2_funct_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2) ),
    inference(resolution,[],[f502,f72])).

fof(f72,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f502,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | v2_funct_1(k6_partfun1(sK0)) ),
    inference(subsumption_resolution,[],[f501,f239])).

fof(f239,plain,(
    v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f238,f56])).

fof(f238,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f237,f58])).

fof(f237,plain,
    ( ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f236,f64])).

fof(f236,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f225,f62])).

fof(f225,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v2_funct_1(sK2)
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | v1_funct_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f63,f82])).

fof(f82,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f501,plain,
    ( v2_funct_1(k6_partfun1(sK0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f500,f403])).

fof(f403,plain,(
    v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f374,f160])).

fof(f160,plain,
    ( ~ v1_relat_1(sK2)
    | v1_relat_1(k2_funct_1(sK2)) ),
    inference(resolution,[],[f62,f73])).

fof(f73,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f500,plain,
    ( v2_funct_1(k6_partfun1(sK0))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f499,f58])).

fof(f499,plain,
    ( v2_funct_1(k6_partfun1(sK0))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f498,f62])).

fof(f498,plain,
    ( v2_funct_1(k6_partfun1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f496,f374])).

fof(f496,plain,
    ( v2_funct_1(k6_partfun1(sK0))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2)) ),
    inference(superposition,[],[f79,f248])).

fof(f248,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f247,f60])).

fof(f60,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f23])).

fof(f247,plain,
    ( k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f246,f58])).

fof(f246,plain,
    ( ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f245,f56])).

fof(f245,plain,
    ( sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f244,f64])).

fof(f244,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f228,f62])).

fof(f228,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | sK1 != k2_relset_1(sK0,sK1,sK2)
    | ~ v2_funct_1(sK2)
    | k1_xboole_0 = sK1
    | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    inference(resolution,[],[f63,f85])).

fof(f85,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f79,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_funct_1)).

fof(f2689,plain,
    ( ~ v2_funct_1(k6_partfun1(sK0))
    | v2_funct_1(sK3) ),
    inference(backward_demodulation,[],[f2217,f2654])).

fof(f2217,plain,
    ( ~ v2_funct_1(k5_relat_1(sK2,sK3))
    | v2_funct_1(sK3) ),
    inference(forward_demodulation,[],[f2216,f1383])).

fof(f2216,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f2215,f59])).

fof(f59,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f23])).

fof(f2215,plain,
    ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f2214,f55])).

fof(f2214,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK3) ),
    inference(subsumption_resolution,[],[f2211,f53])).

fof(f2211,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3))
    | k1_xboole_0 = sK0
    | v2_funct_1(sK3) ),
    inference(resolution,[],[f261,f54])).

fof(f261,plain,(
    ! [X6,X7] :
      ( ~ v1_funct_2(X6,sK1,X7)
      | ~ v1_funct_1(X6)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6))
      | k1_xboole_0 = X7
      | v2_funct_1(X6) ) ),
    inference(subsumption_resolution,[],[f260,f56])).

fof(f260,plain,(
    ! [X6,X7] :
      ( ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,sK1,X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6))
      | sK1 != k2_relset_1(sK0,sK1,sK2)
      | k1_xboole_0 = X7
      | v2_funct_1(X6) ) ),
    inference(subsumption_resolution,[],[f259,f64])).

fof(f259,plain,(
    ! [X6,X7] :
      ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      | ~ v1_funct_1(X6)
      | ~ v1_funct_2(X6,sK1,X7)
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7)))
      | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6))
      | sK1 != k2_relset_1(sK0,sK1,sK2)
      | k1_xboole_0 = X7
      | v2_funct_1(X6) ) ),
    inference(subsumption_resolution,[],[f234,f62])).

fof(f234,plain,(
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
    inference(resolution,[],[f63,f91])).

fof(f91,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).

fof(f363,plain,(
    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3)) ),
    inference(resolution,[],[f345,f99])).

fof(f99,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0 ) ),
    inference(definition_unfolding,[],[f68,f65])).

fof(f68,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).

fof(f345,plain,(
    v1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f107,f295])).

fof(f107,plain,
    ( ~ v1_relat_1(sK3)
    | v1_relat_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f53,f73])).

fof(f4759,plain,(
    k5_relat_1(sK2,k6_partfun1(sK1)) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) ),
    inference(forward_demodulation,[],[f4750,f3074])).

fof(f3074,plain,(
    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f3069,f2691])).

fof(f3069,plain,
    ( ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(trivial_inequality_removal,[],[f3049])).

fof(f3049,plain,
    ( sK0 != sK0
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f319,f3045])).

fof(f319,plain,
    ( ~ v2_funct_1(sK3)
    | sK0 != k2_relat_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(backward_demodulation,[],[f207,f296])).

fof(f207,plain,
    ( sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f206,f59])).

fof(f206,plain,
    ( sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f205,f55])).

fof(f205,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f193,f53])).

fof(f193,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | sK0 != k2_relset_1(sK1,sK0,sK3)
    | ~ v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    inference(resolution,[],[f54,f85])).

fof(f4750,plain,(
    k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) = k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3))) ),
    inference(resolution,[],[f4711,f345])).

fof(f4711,plain,(
    ! [X48] :
      ( ~ v1_relat_1(X48)
      | k5_relat_1(sK2,k5_relat_1(sK3,X48)) = k5_relat_1(k6_partfun1(sK0),X48) ) ),
    inference(forward_demodulation,[],[f4708,f2654])).

fof(f4708,plain,(
    ! [X48] :
      ( ~ v1_relat_1(X48)
      | k5_relat_1(k5_relat_1(sK2,sK3),X48) = k5_relat_1(sK2,k5_relat_1(sK3,X48)) ) ),
    inference(resolution,[],[f329,f374])).

fof(f329,plain,(
    ! [X2,X3] :
      ( ~ v1_relat_1(X2)
      | ~ v1_relat_1(X3)
      | k5_relat_1(k5_relat_1(X2,sK3),X3) = k5_relat_1(X2,k5_relat_1(sK3,X3)) ) ),
    inference(resolution,[],[f295,f69])).

fof(f69,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).

fof(f2778,plain,(
    sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f2777,f53])).

fof(f2777,plain,
    ( ~ v1_funct_1(sK3)
    | sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    inference(subsumption_resolution,[],[f2755,f295])).

fof(f2755,plain,
    ( ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | sK3 = k2_funct_1(k2_funct_1(sK3)) ),
    inference(resolution,[],[f2691,f75])).

fof(f75,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n023.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:09:21 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.22/0.47  % (20344)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.48  % (20330)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.50  % (20336)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.54  % (20352)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.55  % (20334)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.55  % (20347)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.56  % (20332)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.56  % (20337)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.57  % (20335)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.57  % (20358)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.57  % (20342)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.58  % (20356)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.58  % (20353)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.22/0.58  % (20351)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.58  % (20348)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.58  % (20340)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.59  % (20339)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.59  % (20350)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.60  % (20331)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.60  % (20333)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.61  % (20349)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.61  % (20345)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.62  % (20341)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.62  % (20357)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.62  % (20343)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.22/0.62  % (20359)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.22/0.64  % (20338)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.64  % (20355)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.22/0.64  % (20346)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 1.97/0.65  % (20354)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 2.29/0.66  % (20346)Refutation not found, incomplete strategy% (20346)------------------------------
% 2.29/0.66  % (20346)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.29/0.67  % (20346)Termination reason: Refutation not found, incomplete strategy
% 2.29/0.67  
% 2.29/0.67  % (20346)Memory used [KB]: 10746
% 2.29/0.67  % (20346)Time elapsed: 0.220 s
% 2.29/0.67  % (20346)------------------------------
% 2.29/0.67  % (20346)------------------------------
% 2.59/0.72  % (20347)Refutation found. Thanks to Tanya!
% 2.59/0.72  % SZS status Theorem for theBenchmark
% 2.59/0.72  % SZS output start Proof for theBenchmark
% 2.59/0.72  fof(f4862,plain,(
% 2.59/0.72    $false),
% 2.59/0.72    inference(subsumption_resolution,[],[f4767,f61])).
% 2.59/0.72  fof(f61,plain,(
% 2.59/0.72    sK3 != k2_funct_1(sK2)),
% 2.59/0.72    inference(cnf_transformation,[],[f23])).
% 2.59/0.72  fof(f23,plain,(
% 2.59/0.72    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.59/0.72    inference(flattening,[],[f22])).
% 2.59/0.72  fof(f22,plain,(
% 2.59/0.72    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.59/0.72    inference(ennf_transformation,[],[f21])).
% 2.59/0.72  fof(f21,negated_conjecture,(
% 2.59/0.72    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.59/0.72    inference(negated_conjecture,[],[f20])).
% 2.59/0.72  fof(f20,conjecture,(
% 2.59/0.72    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_funct_2)).
% 2.59/0.72  fof(f4767,plain,(
% 2.59/0.72    sK3 = k2_funct_1(sK2)),
% 2.59/0.72    inference(backward_demodulation,[],[f2778,f4761])).
% 2.59/0.72  fof(f4761,plain,(
% 2.59/0.72    sK2 = k2_funct_1(sK3)),
% 2.59/0.72    inference(forward_demodulation,[],[f4760,f421])).
% 2.59/0.72  fof(f421,plain,(
% 2.59/0.72    sK2 = k5_relat_1(sK2,k6_partfun1(sK1))),
% 2.59/0.72    inference(forward_demodulation,[],[f419,f396])).
% 2.59/0.72  fof(f396,plain,(
% 2.59/0.72    sK1 = k2_relat_1(sK2)),
% 2.59/0.72    inference(forward_demodulation,[],[f375,f56])).
% 2.59/0.72  fof(f56,plain,(
% 2.59/0.72    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.59/0.72    inference(cnf_transformation,[],[f23])).
% 2.59/0.72  fof(f375,plain,(
% 2.59/0.72    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 2.59/0.72    inference(resolution,[],[f64,f81])).
% 2.59/0.72  fof(f81,plain,(
% 2.59/0.72    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 2.59/0.72    inference(cnf_transformation,[],[f38])).
% 2.59/0.72  fof(f38,plain,(
% 2.59/0.72    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.59/0.72    inference(ennf_transformation,[],[f10])).
% 2.59/0.72  fof(f10,axiom,(
% 2.59/0.72    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.59/0.72  fof(f64,plain,(
% 2.59/0.72    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.59/0.72    inference(cnf_transformation,[],[f23])).
% 2.59/0.72  fof(f419,plain,(
% 2.59/0.72    sK2 = k5_relat_1(sK2,k6_partfun1(k2_relat_1(sK2)))),
% 2.59/0.72    inference(resolution,[],[f374,f98])).
% 2.59/0.72  fof(f98,plain,(
% 2.59/0.72    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0) )),
% 2.59/0.72    inference(definition_unfolding,[],[f67,f65])).
% 2.59/0.72  fof(f65,plain,(
% 2.59/0.72    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.59/0.72    inference(cnf_transformation,[],[f15])).
% 2.59/0.72  fof(f15,axiom,(
% 2.59/0.72    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.59/0.72  fof(f67,plain,(
% 2.59/0.72    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0) )),
% 2.59/0.72    inference(cnf_transformation,[],[f24])).
% 2.59/0.72  fof(f24,plain,(
% 2.59/0.72    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 2.59/0.72    inference(ennf_transformation,[],[f3])).
% 2.59/0.72  fof(f3,axiom,(
% 2.59/0.72    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_relat_1)).
% 2.59/0.72  fof(f374,plain,(
% 2.59/0.72    v1_relat_1(sK2)),
% 2.59/0.72    inference(resolution,[],[f64,f80])).
% 2.59/0.72  fof(f80,plain,(
% 2.59/0.72    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 2.59/0.72    inference(cnf_transformation,[],[f37])).
% 2.59/0.72  fof(f37,plain,(
% 2.59/0.72    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.59/0.72    inference(ennf_transformation,[],[f9])).
% 2.59/0.72  fof(f9,axiom,(
% 2.59/0.72    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 2.59/0.72  fof(f4760,plain,(
% 2.59/0.72    k2_funct_1(sK3) = k5_relat_1(sK2,k6_partfun1(sK1))),
% 2.59/0.72    inference(forward_demodulation,[],[f4759,f3060])).
% 2.59/0.72  fof(f3060,plain,(
% 2.59/0.72    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))),
% 2.59/0.72    inference(backward_demodulation,[],[f2781,f3045])).
% 2.59/0.72  fof(f3045,plain,(
% 2.59/0.72    sK0 = k2_relat_1(sK3)),
% 2.59/0.72    inference(subsumption_resolution,[],[f3044,f2687])).
% 2.59/0.72  fof(f2687,plain,(
% 2.59/0.72    r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0))),
% 2.59/0.72    inference(backward_demodulation,[],[f1387,f2654])).
% 2.59/0.72  fof(f2654,plain,(
% 2.59/0.72    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.59/0.72    inference(resolution,[],[f2645,f1389])).
% 2.59/0.72  fof(f1389,plain,(
% 2.59/0.72    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.59/0.72    inference(forward_demodulation,[],[f1386,f1383])).
% 2.59/0.72  fof(f1383,plain,(
% 2.59/0.72    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.59/0.72    inference(subsumption_resolution,[],[f1374,f62])).
% 2.59/0.72  fof(f62,plain,(
% 2.59/0.72    v1_funct_1(sK2)),
% 2.59/0.72    inference(cnf_transformation,[],[f23])).
% 2.59/0.72  fof(f1374,plain,(
% 2.59/0.72    ~v1_funct_1(sK2) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.59/0.72    inference(resolution,[],[f325,f64])).
% 2.59/0.72  fof(f325,plain,(
% 2.59/0.72    ( ! [X12,X10,X11] : (~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) | ~v1_funct_1(X10) | k1_partfun1(X11,X12,sK1,sK0,X10,sK3) = k5_relat_1(X10,sK3)) )),
% 2.59/0.72    inference(subsumption_resolution,[],[f311,f53])).
% 2.59/0.72  fof(f53,plain,(
% 2.59/0.72    v1_funct_1(sK3)),
% 2.59/0.72    inference(cnf_transformation,[],[f23])).
% 2.59/0.72  fof(f311,plain,(
% 2.59/0.72    ( ! [X12,X10,X11] : (~v1_funct_1(X10) | ~m1_subset_1(X10,k1_zfmisc_1(k2_zfmisc_1(X11,X12))) | ~v1_funct_1(sK3) | k1_partfun1(X11,X12,sK1,sK0,X10,sK3) = k5_relat_1(X10,sK3)) )),
% 2.59/0.72    inference(resolution,[],[f55,f94])).
% 2.59/0.72  fof(f94,plain,(
% 2.59/0.72    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)) )),
% 2.59/0.72    inference(cnf_transformation,[],[f50])).
% 2.59/0.72  fof(f50,plain,(
% 2.59/0.72    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.59/0.72    inference(flattening,[],[f49])).
% 2.59/0.72  fof(f49,plain,(
% 2.59/0.72    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.59/0.72    inference(ennf_transformation,[],[f14])).
% 2.59/0.72  fof(f14,axiom,(
% 2.59/0.72    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.59/0.72  fof(f55,plain,(
% 2.59/0.72    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.59/0.72    inference(cnf_transformation,[],[f23])).
% 2.59/0.72  fof(f1386,plain,(
% 2.59/0.72    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.59/0.72    inference(backward_demodulation,[],[f425,f1383])).
% 2.59/0.72  fof(f425,plain,(
% 2.59/0.72    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.59/0.72    inference(subsumption_resolution,[],[f423,f97])).
% 2.59/0.72  fof(f97,plain,(
% 2.59/0.72    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.59/0.72    inference(definition_unfolding,[],[f66,f65])).
% 2.59/0.72  fof(f66,plain,(
% 2.59/0.72    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.59/0.72    inference(cnf_transformation,[],[f12])).
% 2.59/0.72  fof(f12,axiom,(
% 2.59/0.72    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t29_relset_1)).
% 2.59/0.72  fof(f423,plain,(
% 2.59/0.72    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(k6_partfun1(sK0),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.59/0.72    inference(resolution,[],[f57,f93])).
% 2.59/0.72  fof(f93,plain,(
% 2.59/0.72    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | X2 = X3 | ~r2_relset_1(X0,X1,X2,X3)) )),
% 2.59/0.72    inference(cnf_transformation,[],[f48])).
% 2.59/0.72  fof(f48,plain,(
% 2.59/0.72    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.59/0.72    inference(flattening,[],[f47])).
% 2.59/0.72  fof(f47,plain,(
% 2.59/0.72    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.59/0.72    inference(ennf_transformation,[],[f11])).
% 2.59/0.72  fof(f11,axiom,(
% 2.59/0.72    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.59/0.72  fof(f57,plain,(
% 2.59/0.72    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.59/0.72    inference(cnf_transformation,[],[f23])).
% 2.59/0.72  fof(f2645,plain,(
% 2.59/0.72    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.59/0.72    inference(subsumption_resolution,[],[f2644,f55])).
% 2.59/0.72  fof(f2644,plain,(
% 2.59/0.72    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.59/0.72    inference(subsumption_resolution,[],[f2643,f53])).
% 2.59/0.72  fof(f2643,plain,(
% 2.59/0.72    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.59/0.72    inference(subsumption_resolution,[],[f2642,f64])).
% 2.59/0.72  fof(f2642,plain,(
% 2.59/0.72    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.59/0.72    inference(subsumption_resolution,[],[f2641,f62])).
% 2.59/0.72  fof(f2641,plain,(
% 2.59/0.72    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.59/0.72    inference(superposition,[],[f96,f1383])).
% 2.59/0.72  fof(f96,plain,(
% 2.59/0.72    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X4) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))) )),
% 2.59/0.72    inference(cnf_transformation,[],[f52])).
% 2.59/0.72  fof(f52,plain,(
% 2.59/0.72    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.59/0.72    inference(flattening,[],[f51])).
% 2.59/0.72  fof(f51,plain,(
% 2.59/0.72    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.59/0.72    inference(ennf_transformation,[],[f13])).
% 2.59/0.72  fof(f13,axiom,(
% 2.59/0.72    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.59/0.72  fof(f1387,plain,(
% 2.59/0.72    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 2.59/0.72    inference(backward_demodulation,[],[f57,f1383])).
% 2.59/0.72  fof(f3044,plain,(
% 2.59/0.72    ~r2_relset_1(sK0,sK0,k6_partfun1(sK0),k6_partfun1(sK0)) | sK0 = k2_relat_1(sK3)),
% 2.59/0.72    inference(forward_demodulation,[],[f3043,f2685])).
% 2.59/0.72  fof(f2685,plain,(
% 2.59/0.72    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_partfun1(sK0)),
% 2.59/0.72    inference(backward_demodulation,[],[f1383,f2654])).
% 2.59/0.72  fof(f3043,plain,(
% 2.59/0.72    sK0 = k2_relat_1(sK3) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.59/0.72    inference(subsumption_resolution,[],[f3042,f64])).
% 2.59/0.72  fof(f3042,plain,(
% 2.59/0.72    sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.59/0.72    inference(subsumption_resolution,[],[f3039,f62])).
% 2.59/0.72  fof(f3039,plain,(
% 2.59/0.72    ~v1_funct_1(sK2) | sK0 = k2_relat_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.59/0.72    inference(resolution,[],[f321,f63])).
% 2.59/0.72  fof(f63,plain,(
% 2.59/0.72    v1_funct_2(sK2,sK0,sK1)),
% 2.59/0.72    inference(cnf_transformation,[],[f23])).
% 2.59/0.72  fof(f321,plain,(
% 2.59/0.72    ( ! [X0] : (~v1_funct_2(X0,sK0,sK1) | ~v1_funct_1(X0) | sK0 = k2_relat_1(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0))) )),
% 2.59/0.72    inference(backward_demodulation,[],[f212,f296])).
% 2.59/0.72  fof(f296,plain,(
% 2.59/0.72    k2_relset_1(sK1,sK0,sK3) = k2_relat_1(sK3)),
% 2.59/0.72    inference(resolution,[],[f55,f81])).
% 2.59/0.72  fof(f212,plain,(
% 2.59/0.72    ( ! [X0] : (~v1_funct_1(X0) | ~v1_funct_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3)) )),
% 2.59/0.72    inference(subsumption_resolution,[],[f211,f55])).
% 2.59/0.72  fof(f211,plain,(
% 2.59/0.72    ( ! [X0] : (~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3)) )),
% 2.59/0.72    inference(subsumption_resolution,[],[f195,f53])).
% 2.59/0.72  fof(f195,plain,(
% 2.59/0.72    ( ! [X0] : (~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,sK0,sK1) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,X0,sK3),k6_partfun1(sK0)) | sK0 = k2_relset_1(sK1,sK0,sK3)) )),
% 2.59/0.72    inference(resolution,[],[f54,f87])).
% 2.59/0.72  fof(f87,plain,(
% 2.59/0.72    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X3) | ~v1_funct_2(X3,X1,X0) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | k2_relset_1(X0,X1,X2) = X1) )),
% 2.59/0.72    inference(cnf_transformation,[],[f44])).
% 2.59/0.72  fof(f44,plain,(
% 2.59/0.72    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.59/0.72    inference(flattening,[],[f43])).
% 2.59/0.72  fof(f43,plain,(
% 2.59/0.72    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.59/0.72    inference(ennf_transformation,[],[f16])).
% 2.59/0.72  fof(f16,axiom,(
% 2.59/0.72    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_funct_2)).
% 2.59/0.72  fof(f54,plain,(
% 2.59/0.72    v1_funct_2(sK3,sK1,sK0)),
% 2.59/0.72    inference(cnf_transformation,[],[f23])).
% 2.59/0.72  fof(f2781,plain,(
% 2.59/0.72    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(k2_relat_1(sK3)),k2_funct_1(sK3))),
% 2.59/0.72    inference(backward_demodulation,[],[f363,f2780])).
% 2.59/0.72  fof(f2780,plain,(
% 2.59/0.72    k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 2.59/0.72    inference(subsumption_resolution,[],[f2779,f53])).
% 2.59/0.72  fof(f2779,plain,(
% 2.59/0.72    ~v1_funct_1(sK3) | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 2.59/0.72    inference(subsumption_resolution,[],[f2756,f295])).
% 2.59/0.72  fof(f295,plain,(
% 2.59/0.72    v1_relat_1(sK3)),
% 2.59/0.72    inference(resolution,[],[f55,f80])).
% 2.59/0.72  fof(f2756,plain,(
% 2.59/0.72    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | k2_relat_1(sK3) = k1_relat_1(k2_funct_1(sK3))),
% 2.59/0.72    inference(resolution,[],[f2691,f76])).
% 2.59/0.72  fof(f76,plain,(
% 2.59/0.72    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 2.59/0.72    inference(cnf_transformation,[],[f34])).
% 2.59/0.72  fof(f34,plain,(
% 2.59/0.72    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.59/0.72    inference(flattening,[],[f33])).
% 2.59/0.72  fof(f33,plain,(
% 2.59/0.72    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.59/0.72    inference(ennf_transformation,[],[f7])).
% 2.59/0.72  fof(f7,axiom,(
% 2.59/0.72    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 2.59/0.72  fof(f2691,plain,(
% 2.59/0.72    v2_funct_1(sK3)),
% 2.59/0.72    inference(subsumption_resolution,[],[f2689,f510])).
% 2.59/0.72  fof(f510,plain,(
% 2.59/0.72    v2_funct_1(k6_partfun1(sK0))),
% 2.59/0.72    inference(subsumption_resolution,[],[f509,f58])).
% 2.59/0.72  fof(f58,plain,(
% 2.59/0.72    v2_funct_1(sK2)),
% 2.59/0.72    inference(cnf_transformation,[],[f23])).
% 2.59/0.72  fof(f509,plain,(
% 2.59/0.72    v2_funct_1(k6_partfun1(sK0)) | ~v2_funct_1(sK2)),
% 2.59/0.72    inference(subsumption_resolution,[],[f508,f62])).
% 2.59/0.72  fof(f508,plain,(
% 2.59/0.72    v2_funct_1(k6_partfun1(sK0)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2)),
% 2.59/0.72    inference(subsumption_resolution,[],[f503,f374])).
% 2.59/0.72  fof(f503,plain,(
% 2.59/0.72    v2_funct_1(k6_partfun1(sK0)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2)),
% 2.59/0.72    inference(resolution,[],[f502,f72])).
% 2.59/0.72  fof(f72,plain,(
% 2.59/0.72    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | v2_funct_1(k2_funct_1(X0))) )),
% 2.59/0.72    inference(cnf_transformation,[],[f28])).
% 2.59/0.72  fof(f28,plain,(
% 2.59/0.72    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.59/0.72    inference(flattening,[],[f27])).
% 2.59/0.72  fof(f27,plain,(
% 2.59/0.72    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.59/0.72    inference(ennf_transformation,[],[f5])).
% 2.59/0.72  fof(f5,axiom,(
% 2.59/0.72    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 2.59/0.72  fof(f502,plain,(
% 2.59/0.72    ~v2_funct_1(k2_funct_1(sK2)) | v2_funct_1(k6_partfun1(sK0))),
% 2.59/0.72    inference(subsumption_resolution,[],[f501,f239])).
% 2.59/0.72  fof(f239,plain,(
% 2.59/0.72    v1_funct_1(k2_funct_1(sK2))),
% 2.59/0.72    inference(subsumption_resolution,[],[f238,f56])).
% 2.59/0.72  fof(f238,plain,(
% 2.59/0.72    sK1 != k2_relset_1(sK0,sK1,sK2) | v1_funct_1(k2_funct_1(sK2))),
% 2.59/0.72    inference(subsumption_resolution,[],[f237,f58])).
% 2.59/0.72  fof(f237,plain,(
% 2.59/0.72    ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | v1_funct_1(k2_funct_1(sK2))),
% 2.59/0.72    inference(subsumption_resolution,[],[f236,f64])).
% 2.59/0.72  fof(f236,plain,(
% 2.59/0.72    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | v1_funct_1(k2_funct_1(sK2))),
% 2.59/0.72    inference(subsumption_resolution,[],[f225,f62])).
% 2.59/0.72  fof(f225,plain,(
% 2.59/0.72    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v2_funct_1(sK2) | sK1 != k2_relset_1(sK0,sK1,sK2) | v1_funct_1(k2_funct_1(sK2))),
% 2.59/0.72    inference(resolution,[],[f63,f82])).
% 2.59/0.72  fof(f82,plain,(
% 2.59/0.72    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2))) )),
% 2.59/0.72    inference(cnf_transformation,[],[f40])).
% 2.59/0.72  fof(f40,plain,(
% 2.59/0.72    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.59/0.72    inference(flattening,[],[f39])).
% 2.59/0.72  fof(f39,plain,(
% 2.59/0.72    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.59/0.72    inference(ennf_transformation,[],[f18])).
% 2.59/0.72  fof(f18,axiom,(
% 2.59/0.72    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 2.59/0.72  fof(f501,plain,(
% 2.59/0.72    v2_funct_1(k6_partfun1(sK0)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2))),
% 2.59/0.72    inference(subsumption_resolution,[],[f500,f403])).
% 2.59/0.72  fof(f403,plain,(
% 2.59/0.72    v1_relat_1(k2_funct_1(sK2))),
% 2.59/0.72    inference(resolution,[],[f374,f160])).
% 2.59/0.72  fof(f160,plain,(
% 2.59/0.72    ~v1_relat_1(sK2) | v1_relat_1(k2_funct_1(sK2))),
% 2.59/0.72    inference(resolution,[],[f62,f73])).
% 2.59/0.72  fof(f73,plain,(
% 2.59/0.72    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 2.59/0.72    inference(cnf_transformation,[],[f30])).
% 2.59/0.72  fof(f30,plain,(
% 2.59/0.72    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.59/0.72    inference(flattening,[],[f29])).
% 2.59/0.72  fof(f29,plain,(
% 2.59/0.72    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.59/0.72    inference(ennf_transformation,[],[f4])).
% 2.59/0.72  fof(f4,axiom,(
% 2.59/0.72    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 2.59/0.72  fof(f500,plain,(
% 2.59/0.72    v2_funct_1(k6_partfun1(sK0)) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2))),
% 2.59/0.72    inference(subsumption_resolution,[],[f499,f58])).
% 2.59/0.72  fof(f499,plain,(
% 2.59/0.72    v2_funct_1(k6_partfun1(sK0)) | ~v2_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2))),
% 2.59/0.72    inference(subsumption_resolution,[],[f498,f62])).
% 2.59/0.72  fof(f498,plain,(
% 2.59/0.72    v2_funct_1(k6_partfun1(sK0)) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2))),
% 2.59/0.72    inference(subsumption_resolution,[],[f496,f374])).
% 2.59/0.72  fof(f496,plain,(
% 2.59/0.72    v2_funct_1(k6_partfun1(sK0)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2))),
% 2.59/0.72    inference(superposition,[],[f79,f248])).
% 2.59/0.72  fof(f248,plain,(
% 2.59/0.72    k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.59/0.72    inference(subsumption_resolution,[],[f247,f60])).
% 2.59/0.72  fof(f60,plain,(
% 2.59/0.72    k1_xboole_0 != sK1),
% 2.59/0.72    inference(cnf_transformation,[],[f23])).
% 2.59/0.72  fof(f247,plain,(
% 2.59/0.72    k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.59/0.72    inference(subsumption_resolution,[],[f246,f58])).
% 2.59/0.72  fof(f246,plain,(
% 2.59/0.72    ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.59/0.72    inference(subsumption_resolution,[],[f245,f56])).
% 2.59/0.72  fof(f245,plain,(
% 2.59/0.72    sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.59/0.72    inference(subsumption_resolution,[],[f244,f64])).
% 2.59/0.72  fof(f244,plain,(
% 2.59/0.72    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.59/0.72    inference(subsumption_resolution,[],[f228,f62])).
% 2.59/0.72  fof(f228,plain,(
% 2.59/0.72    ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | sK1 != k2_relset_1(sK0,sK1,sK2) | ~v2_funct_1(sK2) | k1_xboole_0 = sK1 | k6_partfun1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 2.59/0.72    inference(resolution,[],[f63,f85])).
% 2.59/0.72  fof(f85,plain,(
% 2.59/0.72    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) )),
% 2.59/0.72    inference(cnf_transformation,[],[f42])).
% 2.59/0.72  fof(f42,plain,(
% 2.59/0.72    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 2.59/0.72    inference(flattening,[],[f41])).
% 2.59/0.72  fof(f41,plain,(
% 2.59/0.72    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 2.59/0.72    inference(ennf_transformation,[],[f19])).
% 2.59/0.72  fof(f19,axiom,(
% 2.59/0.72    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 2.59/0.72  fof(f79,plain,(
% 2.59/0.72    ( ! [X0,X1] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X1) | ~v1_funct_1(X1) | ~v2_funct_1(X1) | v2_funct_1(k5_relat_1(X0,X1))) )),
% 2.59/0.72    inference(cnf_transformation,[],[f36])).
% 2.59/0.72  fof(f36,plain,(
% 2.59/0.72    ! [X0,X1] : ((v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.59/0.72    inference(flattening,[],[f35])).
% 2.59/0.72  fof(f35,plain,(
% 2.59/0.72    ! [X0,X1] : ((v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))) | (~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.59/0.72    inference(ennf_transformation,[],[f6])).
% 2.59/0.72  fof(f6,axiom,(
% 2.59/0.72    ! [X0,X1] : ((v2_funct_1(X1) & v1_funct_1(X1) & v1_relat_1(X1) & v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k5_relat_1(X0,X1)) & v1_relat_1(k5_relat_1(X0,X1))))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc7_funct_1)).
% 2.59/0.72  fof(f2689,plain,(
% 2.59/0.72    ~v2_funct_1(k6_partfun1(sK0)) | v2_funct_1(sK3)),
% 2.59/0.72    inference(backward_demodulation,[],[f2217,f2654])).
% 2.59/0.72  fof(f2217,plain,(
% 2.59/0.72    ~v2_funct_1(k5_relat_1(sK2,sK3)) | v2_funct_1(sK3)),
% 2.59/0.72    inference(forward_demodulation,[],[f2216,f1383])).
% 2.59/0.72  fof(f2216,plain,(
% 2.59/0.72    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | v2_funct_1(sK3)),
% 2.59/0.72    inference(subsumption_resolution,[],[f2215,f59])).
% 2.59/0.72  fof(f59,plain,(
% 2.59/0.72    k1_xboole_0 != sK0),
% 2.59/0.72    inference(cnf_transformation,[],[f23])).
% 2.59/0.72  fof(f2215,plain,(
% 2.59/0.72    ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | v2_funct_1(sK3)),
% 2.59/0.72    inference(subsumption_resolution,[],[f2214,f55])).
% 2.59/0.72  fof(f2214,plain,(
% 2.59/0.72    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | v2_funct_1(sK3)),
% 2.59/0.72    inference(subsumption_resolution,[],[f2211,f53])).
% 2.59/0.72  fof(f2211,plain,(
% 2.59/0.72    ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3)) | k1_xboole_0 = sK0 | v2_funct_1(sK3)),
% 2.59/0.72    inference(resolution,[],[f261,f54])).
% 2.59/0.72  fof(f261,plain,(
% 2.59/0.72    ( ! [X6,X7] : (~v1_funct_2(X6,sK1,X7) | ~v1_funct_1(X6) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6)) | k1_xboole_0 = X7 | v2_funct_1(X6)) )),
% 2.59/0.72    inference(subsumption_resolution,[],[f260,f56])).
% 2.59/0.72  fof(f260,plain,(
% 2.59/0.72    ( ! [X6,X7] : (~v1_funct_1(X6) | ~v1_funct_2(X6,sK1,X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6)) | sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = X7 | v2_funct_1(X6)) )),
% 2.59/0.72    inference(subsumption_resolution,[],[f259,f64])).
% 2.59/0.72  fof(f259,plain,(
% 2.59/0.72    ( ! [X6,X7] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X6) | ~v1_funct_2(X6,sK1,X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6)) | sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = X7 | v2_funct_1(X6)) )),
% 2.59/0.72    inference(subsumption_resolution,[],[f234,f62])).
% 2.59/0.72  fof(f234,plain,(
% 2.59/0.72    ( ! [X6,X7] : (~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(X6) | ~v1_funct_2(X6,sK1,X7) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(sK1,X7))) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X7,sK2,X6)) | sK1 != k2_relset_1(sK0,sK1,sK2) | k1_xboole_0 = X7 | v2_funct_1(X6)) )),
% 2.59/0.72    inference(resolution,[],[f63,f91])).
% 2.59/0.72  fof(f91,plain,(
% 2.59/0.72    ( ! [X4,X2,X0,X3,X1] : (~v1_funct_1(X3) | ~v1_funct_2(X3,X0,X1) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~v1_funct_2(X4,X1,X2) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4)) )),
% 2.59/0.72    inference(cnf_transformation,[],[f46])).
% 2.59/0.72  fof(f46,plain,(
% 2.59/0.72    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 2.59/0.72    inference(flattening,[],[f45])).
% 2.59/0.72  fof(f45,plain,(
% 2.59/0.72    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 2.59/0.72    inference(ennf_transformation,[],[f17])).
% 2.59/0.72  fof(f17,axiom,(
% 2.59/0.72    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t30_funct_2)).
% 2.59/0.72  fof(f363,plain,(
% 2.59/0.72    k2_funct_1(sK3) = k5_relat_1(k6_partfun1(k1_relat_1(k2_funct_1(sK3))),k2_funct_1(sK3))),
% 2.59/0.72    inference(resolution,[],[f345,f99])).
% 2.59/0.72  fof(f99,plain,(
% 2.59/0.72    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_partfun1(k1_relat_1(X0)),X0) = X0) )),
% 2.59/0.72    inference(definition_unfolding,[],[f68,f65])).
% 2.59/0.72  fof(f68,plain,(
% 2.59/0.72    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0) )),
% 2.59/0.72    inference(cnf_transformation,[],[f25])).
% 2.59/0.72  fof(f25,plain,(
% 2.59/0.72    ! [X0] : (k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0 | ~v1_relat_1(X0))),
% 2.59/0.72    inference(ennf_transformation,[],[f2])).
% 2.59/0.72  fof(f2,axiom,(
% 2.59/0.72    ! [X0] : (v1_relat_1(X0) => k5_relat_1(k6_relat_1(k1_relat_1(X0)),X0) = X0)),
% 2.59/0.72    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_relat_1)).
% 2.59/0.72  fof(f345,plain,(
% 2.59/0.72    v1_relat_1(k2_funct_1(sK3))),
% 2.59/0.72    inference(resolution,[],[f107,f295])).
% 2.59/0.72  fof(f107,plain,(
% 2.59/0.72    ~v1_relat_1(sK3) | v1_relat_1(k2_funct_1(sK3))),
% 2.59/0.72    inference(resolution,[],[f53,f73])).
% 2.59/0.72  fof(f4759,plain,(
% 2.59/0.72    k5_relat_1(sK2,k6_partfun1(sK1)) = k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3))),
% 2.59/0.72    inference(forward_demodulation,[],[f4750,f3074])).
% 2.59/0.72  fof(f3074,plain,(
% 2.59/0.72    k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.59/0.72    inference(subsumption_resolution,[],[f3069,f2691])).
% 2.59/0.72  fof(f3069,plain,(
% 2.59/0.72    ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.59/0.72    inference(trivial_inequality_removal,[],[f3049])).
% 2.59/0.72  fof(f3049,plain,(
% 2.59/0.72    sK0 != sK0 | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.59/0.72    inference(backward_demodulation,[],[f319,f3045])).
% 2.59/0.72  fof(f319,plain,(
% 2.59/0.72    ~v2_funct_1(sK3) | sK0 != k2_relat_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.59/0.72    inference(backward_demodulation,[],[f207,f296])).
% 2.59/0.72  fof(f207,plain,(
% 2.59/0.72    sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.59/0.72    inference(subsumption_resolution,[],[f206,f59])).
% 2.59/0.72  fof(f206,plain,(
% 2.59/0.72    sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.59/0.72    inference(subsumption_resolution,[],[f205,f55])).
% 2.59/0.73  fof(f205,plain,(
% 2.59/0.73    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.59/0.73    inference(subsumption_resolution,[],[f193,f53])).
% 2.59/0.73  fof(f193,plain,(
% 2.59/0.73    ~v1_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | sK0 != k2_relset_1(sK1,sK0,sK3) | ~v2_funct_1(sK3) | k1_xboole_0 = sK0 | k6_partfun1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 2.59/0.73    inference(resolution,[],[f54,f85])).
% 2.59/0.73  fof(f4750,plain,(
% 2.59/0.73    k5_relat_1(k6_partfun1(sK0),k2_funct_1(sK3)) = k5_relat_1(sK2,k5_relat_1(sK3,k2_funct_1(sK3)))),
% 2.59/0.73    inference(resolution,[],[f4711,f345])).
% 2.59/0.73  fof(f4711,plain,(
% 2.59/0.73    ( ! [X48] : (~v1_relat_1(X48) | k5_relat_1(sK2,k5_relat_1(sK3,X48)) = k5_relat_1(k6_partfun1(sK0),X48)) )),
% 2.59/0.73    inference(forward_demodulation,[],[f4708,f2654])).
% 2.59/0.73  fof(f4708,plain,(
% 2.59/0.73    ( ! [X48] : (~v1_relat_1(X48) | k5_relat_1(k5_relat_1(sK2,sK3),X48) = k5_relat_1(sK2,k5_relat_1(sK3,X48))) )),
% 2.59/0.73    inference(resolution,[],[f329,f374])).
% 2.59/0.73  fof(f329,plain,(
% 2.59/0.73    ( ! [X2,X3] : (~v1_relat_1(X2) | ~v1_relat_1(X3) | k5_relat_1(k5_relat_1(X2,sK3),X3) = k5_relat_1(X2,k5_relat_1(sK3,X3))) )),
% 2.59/0.73    inference(resolution,[],[f295,f69])).
% 2.59/0.73  fof(f69,plain,(
% 2.59/0.73    ( ! [X2,X0,X1] : (~v1_relat_1(X0) | ~v1_relat_1(X1) | ~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))) )),
% 2.59/0.73    inference(cnf_transformation,[],[f26])).
% 2.59/0.73  fof(f26,plain,(
% 2.59/0.73    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.59/0.73    inference(ennf_transformation,[],[f1])).
% 2.59/0.73  fof(f1,axiom,(
% 2.59/0.73    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.59/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_relat_1)).
% 2.59/0.73  fof(f2778,plain,(
% 2.59/0.73    sK3 = k2_funct_1(k2_funct_1(sK3))),
% 2.59/0.73    inference(subsumption_resolution,[],[f2777,f53])).
% 2.59/0.73  fof(f2777,plain,(
% 2.59/0.73    ~v1_funct_1(sK3) | sK3 = k2_funct_1(k2_funct_1(sK3))),
% 2.59/0.73    inference(subsumption_resolution,[],[f2755,f295])).
% 2.59/0.73  fof(f2755,plain,(
% 2.59/0.73    ~v1_relat_1(sK3) | ~v1_funct_1(sK3) | sK3 = k2_funct_1(k2_funct_1(sK3))),
% 2.59/0.73    inference(resolution,[],[f2691,f75])).
% 2.59/0.73  fof(f75,plain,(
% 2.59/0.73    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0) )),
% 2.59/0.73    inference(cnf_transformation,[],[f32])).
% 2.59/0.73  fof(f32,plain,(
% 2.59/0.73    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.59/0.73    inference(flattening,[],[f31])).
% 2.59/0.73  fof(f31,plain,(
% 2.59/0.73    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.59/0.73    inference(ennf_transformation,[],[f8])).
% 2.59/0.73  fof(f8,axiom,(
% 2.59/0.73    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 2.59/0.73    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 2.59/0.73  % SZS output end Proof for theBenchmark
% 2.59/0.73  % (20347)------------------------------
% 2.59/0.73  % (20347)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.59/0.73  % (20347)Termination reason: Refutation
% 2.59/0.73  
% 2.59/0.73  % (20347)Memory used [KB]: 3198
% 2.59/0.73  % (20347)Time elapsed: 0.228 s
% 2.59/0.73  % (20347)------------------------------
% 2.59/0.73  % (20347)------------------------------
% 2.59/0.73  % (20329)Success in time 0.36 s
%------------------------------------------------------------------------------
