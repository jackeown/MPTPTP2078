%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:49 EST 2020

% Result     : Theorem 2.17s
% Output     : Refutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :  189 (1183 expanded)
%              Number of leaves         :   29 ( 369 expanded)
%              Depth                    :   24
%              Number of atoms          :  547 (9731 expanded)
%              Number of equality atoms :  154 (3238 expanded)
%              Maximal formula depth    :   15 (   4 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f2698,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f307,f681,f801,f1479,f2694])).

fof(f2694,plain,
    ( ~ spl4_7
    | ~ spl4_25 ),
    inference(avatar_contradiction_clause,[],[f2693])).

fof(f2693,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f2692,f254])).

fof(f254,plain,(
    sK3 != k4_relat_1(sK2) ),
    inference(superposition,[],[f83,f252])).

fof(f252,plain,(
    k2_funct_1(sK2) = k4_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f251,f139])).

fof(f139,plain,(
    v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f136,f106])).

fof(f106,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f136,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    inference(resolution,[],[f95,f74])).

fof(f74,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f68])).

fof(f68,plain,
    ( k2_funct_1(sK2) != sK3
    & k1_xboole_0 != sK1
    & k1_xboole_0 != sK0
    & v2_funct_1(sK2)
    & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    & sK1 = k2_relset_1(sK0,sK1,sK2)
    & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    & v1_funct_2(sK3,sK1,sK0)
    & v1_funct_1(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    & v1_funct_2(sK2,sK0,sK1)
    & v1_funct_1(sK2) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f67,f66])).

fof(f66,plain,
    ( ? [X0,X1,X2] :
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
        & v1_funct_1(X2) )
   => ( ? [X3] :
          ( k2_funct_1(sK2) != X3
          & k1_xboole_0 != sK1
          & k1_xboole_0 != sK0
          & v2_funct_1(sK2)
          & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
          & sK1 = k2_relset_1(sK0,sK1,sK2)
          & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
          & v1_funct_2(X3,sK1,sK0)
          & v1_funct_1(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
      & v1_funct_2(sK2,sK0,sK1)
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f67,plain,
    ( ? [X3] :
        ( k2_funct_1(sK2) != X3
        & k1_xboole_0 != sK1
        & k1_xboole_0 != sK0
        & v2_funct_1(sK2)
        & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0))
        & sK1 = k2_relset_1(sK0,sK1,sK2)
        & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
        & v1_funct_2(X3,sK1,sK0)
        & v1_funct_1(X3) )
   => ( k2_funct_1(sK2) != sK3
      & k1_xboole_0 != sK1
      & k1_xboole_0 != sK0
      & v2_funct_1(sK2)
      & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
      & sK1 = k2_relset_1(sK0,sK1,sK2)
      & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
      & v1_funct_2(sK3,sK1,sK0)
      & v1_funct_1(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,(
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
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    inference(ennf_transformation,[],[f30])).

fof(f30,negated_conjecture,(
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
    inference(negated_conjecture,[],[f29])).

fof(f29,conjecture,(
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

fof(f95,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f251,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f250,f72])).

fof(f72,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

fof(f250,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f101,f80])).

fof(f80,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f68])).

fof(f101,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f83,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f68])).

fof(f2692,plain,
    ( sK3 = k4_relat_1(sK2)
    | ~ spl4_7
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f2691,f218])).

fof(f218,plain,(
    sK3 = k7_relat_1(sK3,sK1) ),
    inference(subsumption_resolution,[],[f215,f140])).

fof(f140,plain,(
    v1_relat_1(sK3) ),
    inference(subsumption_resolution,[],[f137,f106])).

fof(f137,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0)) ),
    inference(resolution,[],[f95,f77])).

fof(f77,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f68])).

fof(f215,plain,
    ( sK3 = k7_relat_1(sK3,sK1)
    | ~ v1_relat_1(sK3) ),
    inference(resolution,[],[f111,f188])).

fof(f188,plain,(
    v4_relat_1(sK3,sK1) ),
    inference(resolution,[],[f116,f77])).

fof(f116,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f21])).

fof(f21,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f111,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | k7_relat_1(X1,X0) = X1
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = X1
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => k7_relat_1(X1,X0) = X1 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).

fof(f2691,plain,
    ( k7_relat_1(sK3,sK1) = k4_relat_1(sK2)
    | ~ spl4_7
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f2690,f1559])).

fof(f1559,plain,
    ( k4_relat_1(sK2) = k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0))
    | ~ spl4_7
    | ~ spl4_25 ),
    inference(backward_demodulation,[],[f539,f1516])).

fof(f1516,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f1515,f125])).

fof(f125,plain,(
    ! [X0] : k2_relat_1(k6_partfun1(X0)) = X0 ),
    inference(definition_unfolding,[],[f88,f84])).

fof(f84,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f88,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f1515,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0))
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f1514,f123])).

fof(f123,plain,(
    ! [X0] : k6_partfun1(X0) = k4_relat_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f85,f84,f84])).

fof(f85,plain,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).

fof(f1514,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k4_relat_1(k6_partfun1(sK0)))
    | ~ spl4_25 ),
    inference(forward_demodulation,[],[f800,f1461])).

fof(f1461,plain,(
    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) ),
    inference(global_subsumption,[],[f1418,f1460])).

fof(f1460,plain,
    ( k6_partfun1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(resolution,[],[f1412,f450])).

fof(f450,plain,(
    ! [X4,X3] :
      ( ~ r2_relset_1(X3,X3,X4,k6_partfun1(X3))
      | k6_partfun1(X3) = X4
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X3))) ) ),
    inference(resolution,[],[f118,f124])).

fof(f124,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(definition_unfolding,[],[f86,f84])).

fof(f86,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).

fof(f118,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f71])).

fof(f71,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f61])).

fof(f61,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f60])).

fof(f60,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f1412,plain,(
    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0)) ),
    inference(backward_demodulation,[],[f79,f1121])).

fof(f1121,plain,(
    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) ),
    inference(subsumption_resolution,[],[f1114,f72])).

fof(f1114,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)
    | ~ v1_funct_1(sK2) ),
    inference(resolution,[],[f474,f74])).

fof(f474,plain,(
    ! [X19,X17,X18] :
      ( ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | k1_partfun1(X17,X18,sK1,sK0,X19,sK3) = k5_relat_1(X19,sK3)
      | ~ v1_funct_1(X19) ) ),
    inference(subsumption_resolution,[],[f469,f75])).

fof(f75,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f68])).

fof(f469,plain,(
    ! [X19,X17,X18] :
      ( k1_partfun1(X17,X18,sK1,sK0,X19,sK3) = k5_relat_1(X19,sK3)
      | ~ v1_funct_1(sK3)
      | ~ m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18)))
      | ~ v1_funct_1(X19) ) ),
    inference(resolution,[],[f120,f77])).

fof(f120,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f63])).

fof(f63,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f62])).

fof(f62,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f26])).

fof(f26,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f79,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f68])).

fof(f1418,plain,(
    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(subsumption_resolution,[],[f1417,f72])).

fof(f1417,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f1416,f74])).

fof(f1416,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f1415,f75])).

fof(f1415,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f1413,f77])).

fof(f1413,plain,
    ( m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2) ),
    inference(superposition,[],[f122,f1121])).

fof(f122,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f64])).

fof(f64,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f25])).

fof(f25,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f800,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k4_relat_1(k5_relat_1(sK2,sK3)))
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f798])).

fof(f798,plain,
    ( spl4_25
  <=> k1_relat_1(sK2) = k2_relat_1(k4_relat_1(k5_relat_1(sK2,sK3))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f539,plain,
    ( k4_relat_1(sK2) = k5_relat_1(k4_relat_1(sK2),k6_partfun1(k1_relat_1(sK2)))
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f310,f316])).

fof(f316,plain,(
    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f315,f252])).

fof(f315,plain,(
    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    inference(subsumption_resolution,[],[f314,f139])).

fof(f314,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f313,f72])).

fof(f313,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f103,f80])).

fof(f103,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f310,plain,
    ( k4_relat_1(sK2) = k5_relat_1(k4_relat_1(sK2),k6_partfun1(k2_relat_1(k4_relat_1(sK2))))
    | ~ spl4_7 ),
    inference(resolution,[],[f292,f127])).

fof(f127,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0 ) ),
    inference(definition_unfolding,[],[f91,f84])).

fof(f91,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).

fof(f292,plain,
    ( v1_relat_1(k4_relat_1(sK2))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl4_7
  <=> v1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f2690,plain,
    ( k7_relat_1(sK3,sK1) = k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0))
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f2689,f225])).

fof(f225,plain,(
    ! [X10] : k7_relat_1(sK3,X10) = k5_relat_1(k6_partfun1(X10),sK3) ),
    inference(resolution,[],[f130,f140])).

fof(f130,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1) ) ),
    inference(definition_unfolding,[],[f107,f84])).

fof(f107,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).

fof(f2689,plain,
    ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3)
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f2673,f380])).

fof(f380,plain,(
    k6_partfun1(sK1) = k5_relat_1(k4_relat_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f379,f333])).

fof(f333,plain,(
    sK1 = k2_relat_1(sK2) ),
    inference(forward_demodulation,[],[f330,f78])).

fof(f78,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f68])).

fof(f330,plain,(
    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2) ),
    inference(resolution,[],[f115,f74])).

fof(f115,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f22])).

fof(f22,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f379,plain,(
    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k4_relat_1(sK2),sK2) ),
    inference(forward_demodulation,[],[f378,f252])).

fof(f378,plain,(
    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) ),
    inference(subsumption_resolution,[],[f377,f139])).

fof(f377,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f376,f72])).

fof(f376,plain,
    ( k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f128,f80])).

fof(f128,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f105,f84])).

fof(f105,plain,(
    ! [X0] :
      ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0] :
      ( ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0)
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f2673,plain,
    ( k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),sK2),sK3)
    | ~ spl4_7 ),
    inference(resolution,[],[f2517,f292])).

fof(f2517,plain,(
    ! [X26] :
      ( ~ v1_relat_1(X26)
      | k5_relat_1(k5_relat_1(X26,sK2),sK3) = k5_relat_1(X26,k6_partfun1(sK0)) ) ),
    inference(forward_demodulation,[],[f2514,f1461])).

fof(f2514,plain,(
    ! [X26] :
      ( k5_relat_1(k5_relat_1(X26,sK2),sK3) = k5_relat_1(X26,k5_relat_1(sK2,sK3))
      | ~ v1_relat_1(X26) ) ),
    inference(resolution,[],[f406,f139])).

fof(f406,plain,(
    ! [X17,X18] :
      ( ~ v1_relat_1(X18)
      | k5_relat_1(k5_relat_1(X17,X18),sK3) = k5_relat_1(X17,k5_relat_1(X18,sK3))
      | ~ v1_relat_1(X17) ) ),
    inference(resolution,[],[f94,f140])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_relat_1(X2)
      | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2))
              | ~ v1_relat_1(X2) )
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ! [X2] :
              ( v1_relat_1(X2)
             => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).

fof(f1479,plain,
    ( ~ spl4_7
    | spl4_24 ),
    inference(avatar_contradiction_clause,[],[f1478])).

fof(f1478,plain,
    ( $false
    | ~ spl4_7
    | spl4_24 ),
    inference(subsumption_resolution,[],[f1477,f734])).

fof(f734,plain,
    ( r1_tarski(k1_relat_1(sK2),sK0)
    | ~ spl4_7 ),
    inference(forward_demodulation,[],[f732,f316])).

fof(f732,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0)
    | ~ spl4_7 ),
    inference(superposition,[],[f726,f217])).

fof(f217,plain,(
    sK2 = k7_relat_1(sK2,sK0) ),
    inference(subsumption_resolution,[],[f214,f139])).

fof(f214,plain,
    ( sK2 = k7_relat_1(sK2,sK0)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f111,f187])).

fof(f187,plain,(
    v4_relat_1(sK2,sK0) ),
    inference(resolution,[],[f116,f74])).

fof(f726,plain,
    ( ! [X0] : r1_tarski(k2_relat_1(k4_relat_1(k7_relat_1(sK2,X0))),X0)
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f723,f292])).

fof(f723,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k4_relat_1(k7_relat_1(sK2,X0))),X0)
      | ~ v1_relat_1(k4_relat_1(sK2)) ) ),
    inference(superposition,[],[f242,f566])).

fof(f566,plain,(
    ! [X4] : k5_relat_1(k4_relat_1(sK2),k6_partfun1(X4)) = k4_relat_1(k7_relat_1(sK2,X4)) ),
    inference(forward_demodulation,[],[f565,f224])).

fof(f224,plain,(
    ! [X9] : k7_relat_1(sK2,X9) = k5_relat_1(k6_partfun1(X9),sK2) ),
    inference(resolution,[],[f130,f139])).

fof(f565,plain,(
    ! [X4] : k4_relat_1(k5_relat_1(k6_partfun1(X4),sK2)) = k5_relat_1(k4_relat_1(sK2),k6_partfun1(X4)) ),
    inference(forward_demodulation,[],[f560,f123])).

fof(f560,plain,(
    ! [X4] : k4_relat_1(k5_relat_1(k6_partfun1(X4),sK2)) = k5_relat_1(k4_relat_1(sK2),k4_relat_1(k6_partfun1(X4))) ),
    inference(resolution,[],[f361,f141])).

fof(f141,plain,(
    ! [X0] : v1_relat_1(k6_partfun1(X0)) ),
    inference(subsumption_resolution,[],[f138,f106])).

fof(f138,plain,(
    ! [X0] :
      ( v1_relat_1(k6_partfun1(X0))
      | ~ v1_relat_1(k2_zfmisc_1(X0,X0)) ) ),
    inference(resolution,[],[f95,f124])).

fof(f361,plain,(
    ! [X10] :
      ( ~ v1_relat_1(X10)
      | k4_relat_1(k5_relat_1(X10,sK2)) = k5_relat_1(k4_relat_1(sK2),k4_relat_1(X10)) ) ),
    inference(resolution,[],[f93,f139])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).

fof(f242,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X1,k6_partfun1(X0))),X0)
      | ~ v1_relat_1(X1) ) ),
    inference(subsumption_resolution,[],[f232,f141])).

fof(f232,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X1,k6_partfun1(X0))),X0)
      | ~ v1_relat_1(k6_partfun1(X0))
      | ~ v1_relat_1(X1) ) ),
    inference(superposition,[],[f92,f125])).

fof(f92,plain,(
    ! [X0,X1] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).

fof(f1477,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),sK0)
    | spl4_24 ),
    inference(forward_demodulation,[],[f1476,f125])).

fof(f1476,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k2_relat_1(k6_partfun1(sK0)))
    | spl4_24 ),
    inference(forward_demodulation,[],[f1464,f123])).

fof(f1464,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k2_relat_1(k4_relat_1(k6_partfun1(sK0))))
    | spl4_24 ),
    inference(backward_demodulation,[],[f796,f1461])).

fof(f796,plain,
    ( ~ r1_tarski(k1_relat_1(sK2),k2_relat_1(k4_relat_1(k5_relat_1(sK2,sK3))))
    | spl4_24 ),
    inference(avatar_component_clause,[],[f794])).

fof(f794,plain,
    ( spl4_24
  <=> r1_tarski(k1_relat_1(sK2),k2_relat_1(k4_relat_1(k5_relat_1(sK2,sK3)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f801,plain,
    ( ~ spl4_24
    | spl4_25
    | ~ spl4_7
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f789,f671,f291,f798,f794])).

fof(f671,plain,
    ( spl4_18
  <=> v1_relat_1(k4_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f789,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k4_relat_1(k5_relat_1(sK2,sK3)))
    | ~ r1_tarski(k1_relat_1(sK2),k2_relat_1(k4_relat_1(k5_relat_1(sK2,sK3))))
    | ~ spl4_7
    | ~ spl4_18 ),
    inference(resolution,[],[f779,f114])).

fof(f114,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X1,X0)
      | X0 = X1
      | ~ r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(flattening,[],[f69])).

fof(f69,plain,(
    ! [X0,X1] :
      ( ( X0 = X1
        | ~ r1_tarski(X1,X0)
        | ~ r1_tarski(X0,X1) )
      & ( ( r1_tarski(X1,X0)
          & r1_tarski(X0,X1) )
        | X0 != X1 ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f779,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(sK2,sK3))),k1_relat_1(sK2))
    | ~ spl4_7
    | ~ spl4_18 ),
    inference(subsumption_resolution,[],[f777,f672])).

fof(f672,plain,
    ( v1_relat_1(k4_relat_1(sK3))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f671])).

fof(f777,plain,
    ( r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(sK2,sK3))),k1_relat_1(sK2))
    | ~ v1_relat_1(k4_relat_1(sK3))
    | ~ spl4_7 ),
    inference(superposition,[],[f323,f773])).

fof(f773,plain,(
    k4_relat_1(k5_relat_1(sK2,sK3)) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2)) ),
    inference(resolution,[],[f362,f139])).

fof(f362,plain,(
    ! [X11] :
      ( ~ v1_relat_1(X11)
      | k4_relat_1(k5_relat_1(X11,sK3)) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(X11)) ) ),
    inference(resolution,[],[f93,f140])).

fof(f323,plain,
    ( ! [X0] :
        ( r1_tarski(k2_relat_1(k5_relat_1(X0,k4_relat_1(sK2))),k1_relat_1(sK2))
        | ~ v1_relat_1(X0) )
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f318,f292])).

fof(f318,plain,(
    ! [X0] :
      ( r1_tarski(k2_relat_1(k5_relat_1(X0,k4_relat_1(sK2))),k1_relat_1(sK2))
      | ~ v1_relat_1(k4_relat_1(sK2))
      | ~ v1_relat_1(X0) ) ),
    inference(superposition,[],[f92,f316])).

fof(f681,plain,(
    spl4_18 ),
    inference(avatar_contradiction_clause,[],[f680])).

fof(f680,plain,
    ( $false
    | spl4_18 ),
    inference(subsumption_resolution,[],[f679,f140])).

fof(f679,plain,
    ( ~ v1_relat_1(sK3)
    | spl4_18 ),
    inference(resolution,[],[f673,f89])).

fof(f89,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( v1_relat_1(k4_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => v1_relat_1(k4_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).

fof(f673,plain,
    ( ~ v1_relat_1(k4_relat_1(sK3))
    | spl4_18 ),
    inference(avatar_component_clause,[],[f671])).

fof(f307,plain,(
    spl4_7 ),
    inference(avatar_contradiction_clause,[],[f306])).

fof(f306,plain,
    ( $false
    | spl4_7 ),
    inference(subsumption_resolution,[],[f305,f139])).

fof(f305,plain,
    ( ~ v1_relat_1(sK2)
    | spl4_7 ),
    inference(resolution,[],[f293,f89])).

fof(f293,plain,
    ( ~ v1_relat_1(k4_relat_1(sK2))
    | spl4_7 ),
    inference(avatar_component_clause,[],[f291])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : run_vampire %s %d
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % WCLimit    : 600
% 0.12/0.33  % DateTime   : Tue Dec  1 20:21:29 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.20/0.49  % (26848)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.20/0.49  % (26864)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 0.20/0.50  % (26842)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.20/0.50  % (26841)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.20/0.50  % (26850)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.20/0.50  % (26845)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.20/0.51  % (26856)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.20/0.51  % (26866)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 0.20/0.52  % (26857)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.20/0.52  % (26863)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.20/0.52  % (26858)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.20/0.52  % (26857)Refutation not found, incomplete strategy% (26857)------------------------------
% 0.20/0.52  % (26857)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (26849)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.20/0.52  % (26855)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.20/0.52  % (26869)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.20/0.52  % (26857)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.52  
% 0.20/0.52  % (26857)Memory used [KB]: 10746
% 0.20/0.52  % (26857)Time elapsed: 0.123 s
% 0.20/0.52  % (26857)------------------------------
% 0.20/0.52  % (26857)------------------------------
% 0.20/0.52  % (26870)lrs+11_3_av=off:bce=on:cond=fast:ep=R:lcm=reverse:lma=on:newcnf=on:nwc=1.3:stl=30:sd=3:ss=axioms:st=1.2:sos=on:sp=occurrence:uhcvi=on_2 on theBenchmark
% 0.20/0.53  % (26843)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.20/0.53  % (26868)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.20/0.53  % (26846)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.53  % (26844)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.20/0.53  % (26851)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.20/0.53  % (26847)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.54  % (26861)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.20/0.54  % (26867)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.20/0.54  % (26860)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.20/0.54  % (26854)dis+1010_7_afr=on:afp=10000:afq=1.1:amm=sco:anc=none:bd=off:bsr=on:cond=on:fsr=off:lma=on:nm=32:newcnf=on:nwc=1:urr=ec_only:updr=off_83 on theBenchmark
% 0.20/0.54  % (26865)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.20/0.54  % (26862)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.20/0.54  % (26859)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.20/0.54  % (26853)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.20/0.54  % (26852)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 2.17/0.65  % (26871)ott+1010_8:1_add=off:afp=4000:afq=1.4:amm=off:anc=all:bd=off:bsr=on:fsr=off:fde=unused:irw=on:lma=on:nwc=4:nicw=on:sac=on:sp=reverse_arity:urr=on:updr=off:uhcvi=on_239 on theBenchmark
% 2.17/0.67  % (26847)Refutation found. Thanks to Tanya!
% 2.17/0.67  % SZS status Theorem for theBenchmark
% 2.17/0.67  % SZS output start Proof for theBenchmark
% 2.17/0.68  fof(f2698,plain,(
% 2.17/0.68    $false),
% 2.17/0.68    inference(avatar_sat_refutation,[],[f307,f681,f801,f1479,f2694])).
% 2.17/0.68  fof(f2694,plain,(
% 2.17/0.68    ~spl4_7 | ~spl4_25),
% 2.17/0.68    inference(avatar_contradiction_clause,[],[f2693])).
% 2.17/0.68  fof(f2693,plain,(
% 2.17/0.68    $false | (~spl4_7 | ~spl4_25)),
% 2.17/0.68    inference(subsumption_resolution,[],[f2692,f254])).
% 2.17/0.68  fof(f254,plain,(
% 2.17/0.68    sK3 != k4_relat_1(sK2)),
% 2.17/0.68    inference(superposition,[],[f83,f252])).
% 2.17/0.68  fof(f252,plain,(
% 2.17/0.68    k2_funct_1(sK2) = k4_relat_1(sK2)),
% 2.17/0.68    inference(subsumption_resolution,[],[f251,f139])).
% 2.17/0.68  fof(f139,plain,(
% 2.17/0.68    v1_relat_1(sK2)),
% 2.17/0.68    inference(subsumption_resolution,[],[f136,f106])).
% 2.17/0.68  fof(f106,plain,(
% 2.17/0.68    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 2.17/0.68    inference(cnf_transformation,[],[f4])).
% 2.17/0.68  fof(f4,axiom,(
% 2.17/0.68    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 2.17/0.68    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 2.17/0.68  fof(f136,plain,(
% 2.17/0.68    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1))),
% 2.17/0.68    inference(resolution,[],[f95,f74])).
% 2.17/0.68  fof(f74,plain,(
% 2.17/0.68    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 2.17/0.68    inference(cnf_transformation,[],[f68])).
% 2.17/0.68  fof(f68,plain,(
% 2.17/0.68    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 2.17/0.68    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f32,f67,f66])).
% 2.17/0.68  fof(f66,plain,(
% 2.17/0.68    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 2.17/0.68    introduced(choice_axiom,[])).
% 2.17/0.68  fof(f67,plain,(
% 2.17/0.68    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 2.17/0.68    introduced(choice_axiom,[])).
% 2.17/0.69  fof(f32,plain,(
% 2.17/0.69    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 2.17/0.69    inference(flattening,[],[f31])).
% 2.17/0.69  fof(f31,plain,(
% 2.17/0.69    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 2.17/0.69    inference(ennf_transformation,[],[f30])).
% 2.17/0.69  fof(f30,negated_conjecture,(
% 2.17/0.69    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.17/0.69    inference(negated_conjecture,[],[f29])).
% 2.17/0.69  fof(f29,conjecture,(
% 2.17/0.69    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 2.17/0.69  fof(f95,plain,(
% 2.17/0.69    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.17/0.69    inference(cnf_transformation,[],[f39])).
% 2.17/0.69  fof(f39,plain,(
% 2.17/0.69    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 2.17/0.69    inference(ennf_transformation,[],[f2])).
% 2.17/0.69  fof(f2,axiom,(
% 2.17/0.69    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 2.17/0.69  fof(f251,plain,(
% 2.17/0.69    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_relat_1(sK2)),
% 2.17/0.69    inference(subsumption_resolution,[],[f250,f72])).
% 2.17/0.69  fof(f72,plain,(
% 2.17/0.69    v1_funct_1(sK2)),
% 2.17/0.69    inference(cnf_transformation,[],[f68])).
% 2.17/0.69  fof(f250,plain,(
% 2.17/0.69    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.17/0.69    inference(resolution,[],[f101,f80])).
% 2.17/0.69  fof(f80,plain,(
% 2.17/0.69    v2_funct_1(sK2)),
% 2.17/0.69    inference(cnf_transformation,[],[f68])).
% 2.17/0.69  fof(f101,plain,(
% 2.17/0.69    ( ! [X0] : (~v2_funct_1(X0) | k4_relat_1(X0) = k2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.17/0.69    inference(cnf_transformation,[],[f45])).
% 2.17/0.69  fof(f45,plain,(
% 2.17/0.69    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.17/0.69    inference(flattening,[],[f44])).
% 2.17/0.69  fof(f44,plain,(
% 2.17/0.69    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.17/0.69    inference(ennf_transformation,[],[f15])).
% 2.17/0.69  fof(f15,axiom,(
% 2.17/0.69    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 2.17/0.69  fof(f83,plain,(
% 2.17/0.69    k2_funct_1(sK2) != sK3),
% 2.17/0.69    inference(cnf_transformation,[],[f68])).
% 2.17/0.69  fof(f2692,plain,(
% 2.17/0.69    sK3 = k4_relat_1(sK2) | (~spl4_7 | ~spl4_25)),
% 2.17/0.69    inference(forward_demodulation,[],[f2691,f218])).
% 2.17/0.69  fof(f218,plain,(
% 2.17/0.69    sK3 = k7_relat_1(sK3,sK1)),
% 2.17/0.69    inference(subsumption_resolution,[],[f215,f140])).
% 2.17/0.69  fof(f140,plain,(
% 2.17/0.69    v1_relat_1(sK3)),
% 2.17/0.69    inference(subsumption_resolution,[],[f137,f106])).
% 2.17/0.69  fof(f137,plain,(
% 2.17/0.69    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0))),
% 2.17/0.69    inference(resolution,[],[f95,f77])).
% 2.17/0.69  fof(f77,plain,(
% 2.17/0.69    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 2.17/0.69    inference(cnf_transformation,[],[f68])).
% 2.17/0.69  fof(f215,plain,(
% 2.17/0.69    sK3 = k7_relat_1(sK3,sK1) | ~v1_relat_1(sK3)),
% 2.17/0.69    inference(resolution,[],[f111,f188])).
% 2.17/0.69  fof(f188,plain,(
% 2.17/0.69    v4_relat_1(sK3,sK1)),
% 2.17/0.69    inference(resolution,[],[f116,f77])).
% 2.17/0.69  fof(f116,plain,(
% 2.17/0.69    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 2.17/0.69    inference(cnf_transformation,[],[f59])).
% 2.17/0.69  fof(f59,plain,(
% 2.17/0.69    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.17/0.69    inference(ennf_transformation,[],[f21])).
% 2.17/0.69  fof(f21,axiom,(
% 2.17/0.69    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 2.17/0.69  fof(f111,plain,(
% 2.17/0.69    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | k7_relat_1(X1,X0) = X1 | ~v1_relat_1(X1)) )),
% 2.17/0.69    inference(cnf_transformation,[],[f57])).
% 2.17/0.69  fof(f57,plain,(
% 2.17/0.69    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 2.17/0.69    inference(flattening,[],[f56])).
% 2.17/0.69  fof(f56,plain,(
% 2.17/0.69    ! [X0,X1] : (k7_relat_1(X1,X0) = X1 | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 2.17/0.69    inference(ennf_transformation,[],[f7])).
% 2.17/0.69  fof(f7,axiom,(
% 2.17/0.69    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => k7_relat_1(X1,X0) = X1)),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t209_relat_1)).
% 2.17/0.69  fof(f2691,plain,(
% 2.17/0.69    k7_relat_1(sK3,sK1) = k4_relat_1(sK2) | (~spl4_7 | ~spl4_25)),
% 2.17/0.69    inference(forward_demodulation,[],[f2690,f1559])).
% 2.17/0.69  fof(f1559,plain,(
% 2.17/0.69    k4_relat_1(sK2) = k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) | (~spl4_7 | ~spl4_25)),
% 2.17/0.69    inference(backward_demodulation,[],[f539,f1516])).
% 2.17/0.69  fof(f1516,plain,(
% 2.17/0.69    sK0 = k1_relat_1(sK2) | ~spl4_25),
% 2.17/0.69    inference(forward_demodulation,[],[f1515,f125])).
% 2.17/0.69  fof(f125,plain,(
% 2.17/0.69    ( ! [X0] : (k2_relat_1(k6_partfun1(X0)) = X0) )),
% 2.17/0.69    inference(definition_unfolding,[],[f88,f84])).
% 2.17/0.69  fof(f84,plain,(
% 2.17/0.69    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 2.17/0.69    inference(cnf_transformation,[],[f27])).
% 2.17/0.69  fof(f27,axiom,(
% 2.17/0.69    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 2.17/0.69  fof(f88,plain,(
% 2.17/0.69    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 2.17/0.69    inference(cnf_transformation,[],[f11])).
% 2.17/0.69  fof(f11,axiom,(
% 2.17/0.69    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 2.17/0.69  fof(f1515,plain,(
% 2.17/0.69    k1_relat_1(sK2) = k2_relat_1(k6_partfun1(sK0)) | ~spl4_25),
% 2.17/0.69    inference(forward_demodulation,[],[f1514,f123])).
% 2.17/0.69  fof(f123,plain,(
% 2.17/0.69    ( ! [X0] : (k6_partfun1(X0) = k4_relat_1(k6_partfun1(X0))) )),
% 2.17/0.69    inference(definition_unfolding,[],[f85,f84,f84])).
% 2.17/0.69  fof(f85,plain,(
% 2.17/0.69    ( ! [X0] : (k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))) )),
% 2.17/0.69    inference(cnf_transformation,[],[f12])).
% 2.17/0.69  fof(f12,axiom,(
% 2.17/0.69    ! [X0] : k6_relat_1(X0) = k4_relat_1(k6_relat_1(X0))),
% 2.17/0.69    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t72_relat_1)).
% 2.17/0.69  fof(f1514,plain,(
% 2.17/0.69    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(k6_partfun1(sK0))) | ~spl4_25),
% 2.17/0.69    inference(forward_demodulation,[],[f800,f1461])).
% 2.17/0.69  fof(f1461,plain,(
% 2.17/0.69    k6_partfun1(sK0) = k5_relat_1(sK2,sK3)),
% 2.17/0.69    inference(global_subsumption,[],[f1418,f1460])).
% 2.17/0.69  fof(f1460,plain,(
% 2.17/0.69    k6_partfun1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.17/0.69    inference(resolution,[],[f1412,f450])).
% 2.17/0.70  fof(f450,plain,(
% 2.17/0.70    ( ! [X4,X3] : (~r2_relset_1(X3,X3,X4,k6_partfun1(X3)) | k6_partfun1(X3) = X4 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X3,X3)))) )),
% 2.17/0.70    inference(resolution,[],[f118,f124])).
% 2.17/0.70  fof(f124,plain,(
% 2.17/0.70    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.17/0.70    inference(definition_unfolding,[],[f86,f84])).
% 2.17/0.70  fof(f86,plain,(
% 2.17/0.70    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 2.17/0.70    inference(cnf_transformation,[],[f24])).
% 2.17/0.70  fof(f24,axiom,(
% 2.17/0.70    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 2.17/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_relset_1)).
% 2.17/0.70  fof(f118,plain,(
% 2.17/0.70    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 2.17/0.70    inference(cnf_transformation,[],[f71])).
% 2.17/0.70  fof(f71,plain,(
% 2.17/0.70    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.17/0.70    inference(nnf_transformation,[],[f61])).
% 2.17/0.70  fof(f61,plain,(
% 2.17/0.70    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.17/0.70    inference(flattening,[],[f60])).
% 2.17/0.70  fof(f60,plain,(
% 2.17/0.70    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 2.17/0.70    inference(ennf_transformation,[],[f23])).
% 2.17/0.70  fof(f23,axiom,(
% 2.17/0.70    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 2.17/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 2.17/0.70  fof(f1412,plain,(
% 2.17/0.70    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_partfun1(sK0))),
% 2.17/0.70    inference(backward_demodulation,[],[f79,f1121])).
% 2.17/0.70  fof(f1121,plain,(
% 2.17/0.70    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3)),
% 2.17/0.70    inference(subsumption_resolution,[],[f1114,f72])).
% 2.17/0.70  fof(f1114,plain,(
% 2.17/0.70    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k5_relat_1(sK2,sK3) | ~v1_funct_1(sK2)),
% 2.17/0.70    inference(resolution,[],[f474,f74])).
% 2.17/0.70  fof(f474,plain,(
% 2.17/0.70    ( ! [X19,X17,X18] : (~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) | k1_partfun1(X17,X18,sK1,sK0,X19,sK3) = k5_relat_1(X19,sK3) | ~v1_funct_1(X19)) )),
% 2.17/0.70    inference(subsumption_resolution,[],[f469,f75])).
% 2.17/0.70  fof(f75,plain,(
% 2.17/0.70    v1_funct_1(sK3)),
% 2.17/0.70    inference(cnf_transformation,[],[f68])).
% 2.17/0.70  fof(f469,plain,(
% 2.17/0.70    ( ! [X19,X17,X18] : (k1_partfun1(X17,X18,sK1,sK0,X19,sK3) = k5_relat_1(X19,sK3) | ~v1_funct_1(sK3) | ~m1_subset_1(X19,k1_zfmisc_1(k2_zfmisc_1(X17,X18))) | ~v1_funct_1(X19)) )),
% 2.17/0.70    inference(resolution,[],[f120,f77])).
% 2.17/0.70  fof(f120,plain,(
% 2.17/0.70    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.17/0.70    inference(cnf_transformation,[],[f63])).
% 2.17/0.70  fof(f63,plain,(
% 2.17/0.70    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.17/0.70    inference(flattening,[],[f62])).
% 2.17/0.70  fof(f62,plain,(
% 2.17/0.70    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.17/0.70    inference(ennf_transformation,[],[f26])).
% 2.17/0.70  fof(f26,axiom,(
% 2.17/0.70    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 2.17/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 2.17/0.70  fof(f79,plain,(
% 2.17/0.70    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 2.17/0.70    inference(cnf_transformation,[],[f68])).
% 2.17/0.70  fof(f1418,plain,(
% 2.17/0.70    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 2.17/0.70    inference(subsumption_resolution,[],[f1417,f72])).
% 2.17/0.70  fof(f1417,plain,(
% 2.17/0.70    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK2)),
% 2.17/0.70    inference(subsumption_resolution,[],[f1416,f74])).
% 2.17/0.70  fof(f1416,plain,(
% 2.17/0.70    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.17/0.70    inference(subsumption_resolution,[],[f1415,f75])).
% 2.17/0.70  fof(f1415,plain,(
% 2.17/0.70    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.17/0.70    inference(subsumption_resolution,[],[f1413,f77])).
% 2.17/0.70  fof(f1413,plain,(
% 2.17/0.70    m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2)),
% 2.17/0.70    inference(superposition,[],[f122,f1121])).
% 2.17/0.70  fof(f122,plain,(
% 2.17/0.70    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 2.17/0.70    inference(cnf_transformation,[],[f65])).
% 2.17/0.70  fof(f65,plain,(
% 2.17/0.70    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 2.17/0.70    inference(flattening,[],[f64])).
% 2.17/0.70  fof(f64,plain,(
% 2.17/0.70    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 2.17/0.70    inference(ennf_transformation,[],[f25])).
% 2.17/0.70  fof(f25,axiom,(
% 2.17/0.70    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 2.17/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 2.17/0.70  fof(f800,plain,(
% 2.17/0.70    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(k5_relat_1(sK2,sK3))) | ~spl4_25),
% 2.17/0.70    inference(avatar_component_clause,[],[f798])).
% 2.17/0.70  fof(f798,plain,(
% 2.17/0.70    spl4_25 <=> k1_relat_1(sK2) = k2_relat_1(k4_relat_1(k5_relat_1(sK2,sK3)))),
% 2.17/0.70    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 2.17/0.70  fof(f539,plain,(
% 2.17/0.70    k4_relat_1(sK2) = k5_relat_1(k4_relat_1(sK2),k6_partfun1(k1_relat_1(sK2))) | ~spl4_7),
% 2.17/0.70    inference(forward_demodulation,[],[f310,f316])).
% 2.17/0.70  fof(f316,plain,(
% 2.17/0.70    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))),
% 2.17/0.70    inference(forward_demodulation,[],[f315,f252])).
% 2.17/0.70  fof(f315,plain,(
% 2.17/0.70    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 2.17/0.70    inference(subsumption_resolution,[],[f314,f139])).
% 2.17/0.70  fof(f314,plain,(
% 2.17/0.70    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2)),
% 2.17/0.70    inference(subsumption_resolution,[],[f313,f72])).
% 2.17/0.70  fof(f313,plain,(
% 2.17/0.70    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.17/0.70    inference(resolution,[],[f103,f80])).
% 2.17/0.70  fof(f103,plain,(
% 2.17/0.70    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.17/0.70    inference(cnf_transformation,[],[f47])).
% 2.17/0.70  fof(f47,plain,(
% 2.17/0.70    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.17/0.70    inference(flattening,[],[f46])).
% 2.17/0.70  fof(f46,plain,(
% 2.17/0.70    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.17/0.70    inference(ennf_transformation,[],[f19])).
% 2.17/0.70  fof(f19,axiom,(
% 2.17/0.70    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 2.17/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 2.17/0.70  fof(f310,plain,(
% 2.17/0.70    k4_relat_1(sK2) = k5_relat_1(k4_relat_1(sK2),k6_partfun1(k2_relat_1(k4_relat_1(sK2)))) | ~spl4_7),
% 2.17/0.70    inference(resolution,[],[f292,f127])).
% 2.17/0.70  fof(f127,plain,(
% 2.17/0.70    ( ! [X0] : (~v1_relat_1(X0) | k5_relat_1(X0,k6_partfun1(k2_relat_1(X0))) = X0) )),
% 2.17/0.70    inference(definition_unfolding,[],[f91,f84])).
% 2.17/0.70  fof(f91,plain,(
% 2.17/0.70    ( ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0)) )),
% 2.17/0.70    inference(cnf_transformation,[],[f35])).
% 2.17/0.70  fof(f35,plain,(
% 2.17/0.70    ! [X0] : (k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0 | ~v1_relat_1(X0))),
% 2.17/0.70    inference(ennf_transformation,[],[f13])).
% 2.17/0.70  fof(f13,axiom,(
% 2.17/0.70    ! [X0] : (v1_relat_1(X0) => k5_relat_1(X0,k6_relat_1(k2_relat_1(X0))) = X0)),
% 2.17/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_relat_1)).
% 2.17/0.70  fof(f292,plain,(
% 2.17/0.70    v1_relat_1(k4_relat_1(sK2)) | ~spl4_7),
% 2.17/0.70    inference(avatar_component_clause,[],[f291])).
% 2.17/0.70  fof(f291,plain,(
% 2.17/0.70    spl4_7 <=> v1_relat_1(k4_relat_1(sK2))),
% 2.17/0.70    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 2.17/0.70  fof(f2690,plain,(
% 2.17/0.70    k7_relat_1(sK3,sK1) = k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) | ~spl4_7),
% 2.17/0.70    inference(forward_demodulation,[],[f2689,f225])).
% 2.17/0.70  fof(f225,plain,(
% 2.17/0.70    ( ! [X10] : (k7_relat_1(sK3,X10) = k5_relat_1(k6_partfun1(X10),sK3)) )),
% 2.17/0.70    inference(resolution,[],[f130,f140])).
% 2.17/0.70  fof(f130,plain,(
% 2.17/0.70    ( ! [X0,X1] : (~v1_relat_1(X1) | k7_relat_1(X1,X0) = k5_relat_1(k6_partfun1(X0),X1)) )),
% 2.17/0.70    inference(definition_unfolding,[],[f107,f84])).
% 2.17/0.70  fof(f107,plain,(
% 2.17/0.70    ( ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1)) )),
% 2.17/0.70    inference(cnf_transformation,[],[f50])).
% 2.17/0.70  fof(f50,plain,(
% 2.17/0.70    ! [X0,X1] : (k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1) | ~v1_relat_1(X1))),
% 2.17/0.70    inference(ennf_transformation,[],[f14])).
% 2.17/0.70  fof(f14,axiom,(
% 2.17/0.70    ! [X0,X1] : (v1_relat_1(X1) => k7_relat_1(X1,X0) = k5_relat_1(k6_relat_1(X0),X1))),
% 2.17/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_relat_1)).
% 2.17/0.70  fof(f2689,plain,(
% 2.17/0.70    k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k6_partfun1(sK1),sK3) | ~spl4_7),
% 2.17/0.70    inference(forward_demodulation,[],[f2673,f380])).
% 2.17/0.70  fof(f380,plain,(
% 2.17/0.70    k6_partfun1(sK1) = k5_relat_1(k4_relat_1(sK2),sK2)),
% 2.17/0.70    inference(forward_demodulation,[],[f379,f333])).
% 2.17/0.70  fof(f333,plain,(
% 2.17/0.70    sK1 = k2_relat_1(sK2)),
% 2.17/0.70    inference(forward_demodulation,[],[f330,f78])).
% 2.17/0.70  fof(f78,plain,(
% 2.17/0.70    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 2.17/0.70    inference(cnf_transformation,[],[f68])).
% 2.17/0.70  fof(f330,plain,(
% 2.17/0.70    k2_relset_1(sK0,sK1,sK2) = k2_relat_1(sK2)),
% 2.17/0.70    inference(resolution,[],[f115,f74])).
% 2.17/0.70  fof(f115,plain,(
% 2.17/0.70    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 2.17/0.70    inference(cnf_transformation,[],[f58])).
% 2.17/0.70  fof(f58,plain,(
% 2.17/0.70    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 2.17/0.70    inference(ennf_transformation,[],[f22])).
% 2.17/0.70  fof(f22,axiom,(
% 2.17/0.70    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 2.17/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 2.17/0.70  fof(f379,plain,(
% 2.17/0.70    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k4_relat_1(sK2),sK2)),
% 2.17/0.70    inference(forward_demodulation,[],[f378,f252])).
% 2.17/0.70  fof(f378,plain,(
% 2.17/0.70    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2)),
% 2.17/0.70    inference(subsumption_resolution,[],[f377,f139])).
% 2.17/0.70  fof(f377,plain,(
% 2.17/0.70    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_relat_1(sK2)),
% 2.17/0.70    inference(subsumption_resolution,[],[f376,f72])).
% 2.17/0.70  fof(f376,plain,(
% 2.17/0.70    k6_partfun1(k2_relat_1(sK2)) = k5_relat_1(k2_funct_1(sK2),sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 2.17/0.70    inference(resolution,[],[f128,f80])).
% 2.17/0.70  fof(f128,plain,(
% 2.17/0.70    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_partfun1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.17/0.70    inference(definition_unfolding,[],[f105,f84])).
% 2.17/0.70  fof(f105,plain,(
% 2.17/0.70    ( ! [X0] : (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 2.17/0.70    inference(cnf_transformation,[],[f49])).
% 2.17/0.70  fof(f49,plain,(
% 2.17/0.70    ! [X0] : ((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 2.17/0.70    inference(flattening,[],[f48])).
% 2.17/0.70  fof(f48,plain,(
% 2.17/0.70    ! [X0] : (((k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 2.17/0.70    inference(ennf_transformation,[],[f20])).
% 2.17/0.70  fof(f20,axiom,(
% 2.17/0.70    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k6_relat_1(k2_relat_1(X0)) = k5_relat_1(k2_funct_1(X0),X0) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 2.17/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 2.17/0.70  fof(f2673,plain,(
% 2.17/0.70    k5_relat_1(k4_relat_1(sK2),k6_partfun1(sK0)) = k5_relat_1(k5_relat_1(k4_relat_1(sK2),sK2),sK3) | ~spl4_7),
% 2.17/0.70    inference(resolution,[],[f2517,f292])).
% 2.17/0.70  fof(f2517,plain,(
% 2.17/0.70    ( ! [X26] : (~v1_relat_1(X26) | k5_relat_1(k5_relat_1(X26,sK2),sK3) = k5_relat_1(X26,k6_partfun1(sK0))) )),
% 2.17/0.70    inference(forward_demodulation,[],[f2514,f1461])).
% 2.17/0.70  fof(f2514,plain,(
% 2.17/0.70    ( ! [X26] : (k5_relat_1(k5_relat_1(X26,sK2),sK3) = k5_relat_1(X26,k5_relat_1(sK2,sK3)) | ~v1_relat_1(X26)) )),
% 2.17/0.70    inference(resolution,[],[f406,f139])).
% 2.17/0.70  fof(f406,plain,(
% 2.17/0.70    ( ! [X17,X18] : (~v1_relat_1(X18) | k5_relat_1(k5_relat_1(X17,X18),sK3) = k5_relat_1(X17,k5_relat_1(X18,sK3)) | ~v1_relat_1(X17)) )),
% 2.17/0.70    inference(resolution,[],[f94,f140])).
% 2.17/0.70  fof(f94,plain,(
% 2.17/0.70    ( ! [X2,X0,X1] : (~v1_relat_1(X2) | k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.17/0.70    inference(cnf_transformation,[],[f38])).
% 2.17/0.70  fof(f38,plain,(
% 2.17/0.70    ! [X0] : (! [X1] : (! [X2] : (k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)) | ~v1_relat_1(X2)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.17/0.70    inference(ennf_transformation,[],[f10])).
% 2.17/0.70  fof(f10,axiom,(
% 2.17/0.70    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => ! [X2] : (v1_relat_1(X2) => k5_relat_1(k5_relat_1(X0,X1),X2) = k5_relat_1(X0,k5_relat_1(X1,X2)))))),
% 2.17/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_relat_1)).
% 2.17/0.70  fof(f1479,plain,(
% 2.17/0.70    ~spl4_7 | spl4_24),
% 2.17/0.70    inference(avatar_contradiction_clause,[],[f1478])).
% 2.17/0.70  fof(f1478,plain,(
% 2.17/0.70    $false | (~spl4_7 | spl4_24)),
% 2.17/0.70    inference(subsumption_resolution,[],[f1477,f734])).
% 2.17/0.70  fof(f734,plain,(
% 2.17/0.70    r1_tarski(k1_relat_1(sK2),sK0) | ~spl4_7),
% 2.17/0.70    inference(forward_demodulation,[],[f732,f316])).
% 2.17/0.70  fof(f732,plain,(
% 2.17/0.70    r1_tarski(k2_relat_1(k4_relat_1(sK2)),sK0) | ~spl4_7),
% 2.17/0.70    inference(superposition,[],[f726,f217])).
% 2.17/0.70  fof(f217,plain,(
% 2.17/0.70    sK2 = k7_relat_1(sK2,sK0)),
% 2.17/0.70    inference(subsumption_resolution,[],[f214,f139])).
% 2.17/0.70  fof(f214,plain,(
% 2.17/0.70    sK2 = k7_relat_1(sK2,sK0) | ~v1_relat_1(sK2)),
% 2.17/0.70    inference(resolution,[],[f111,f187])).
% 2.17/0.70  fof(f187,plain,(
% 2.17/0.70    v4_relat_1(sK2,sK0)),
% 2.17/0.70    inference(resolution,[],[f116,f74])).
% 2.17/0.70  fof(f726,plain,(
% 2.17/0.70    ( ! [X0] : (r1_tarski(k2_relat_1(k4_relat_1(k7_relat_1(sK2,X0))),X0)) ) | ~spl4_7),
% 2.17/0.70    inference(subsumption_resolution,[],[f723,f292])).
% 2.17/0.70  fof(f723,plain,(
% 2.17/0.70    ( ! [X0] : (r1_tarski(k2_relat_1(k4_relat_1(k7_relat_1(sK2,X0))),X0) | ~v1_relat_1(k4_relat_1(sK2))) )),
% 2.17/0.70    inference(superposition,[],[f242,f566])).
% 2.17/0.70  fof(f566,plain,(
% 2.17/0.70    ( ! [X4] : (k5_relat_1(k4_relat_1(sK2),k6_partfun1(X4)) = k4_relat_1(k7_relat_1(sK2,X4))) )),
% 2.17/0.70    inference(forward_demodulation,[],[f565,f224])).
% 2.17/0.70  fof(f224,plain,(
% 2.17/0.70    ( ! [X9] : (k7_relat_1(sK2,X9) = k5_relat_1(k6_partfun1(X9),sK2)) )),
% 2.17/0.70    inference(resolution,[],[f130,f139])).
% 2.17/0.70  fof(f565,plain,(
% 2.17/0.70    ( ! [X4] : (k4_relat_1(k5_relat_1(k6_partfun1(X4),sK2)) = k5_relat_1(k4_relat_1(sK2),k6_partfun1(X4))) )),
% 2.17/0.70    inference(forward_demodulation,[],[f560,f123])).
% 2.17/0.70  fof(f560,plain,(
% 2.17/0.70    ( ! [X4] : (k4_relat_1(k5_relat_1(k6_partfun1(X4),sK2)) = k5_relat_1(k4_relat_1(sK2),k4_relat_1(k6_partfun1(X4)))) )),
% 2.17/0.70    inference(resolution,[],[f361,f141])).
% 2.17/0.70  fof(f141,plain,(
% 2.17/0.70    ( ! [X0] : (v1_relat_1(k6_partfun1(X0))) )),
% 2.17/0.70    inference(subsumption_resolution,[],[f138,f106])).
% 2.17/0.70  fof(f138,plain,(
% 2.17/0.70    ( ! [X0] : (v1_relat_1(k6_partfun1(X0)) | ~v1_relat_1(k2_zfmisc_1(X0,X0))) )),
% 2.17/0.70    inference(resolution,[],[f95,f124])).
% 2.17/0.70  fof(f361,plain,(
% 2.17/0.70    ( ! [X10] : (~v1_relat_1(X10) | k4_relat_1(k5_relat_1(X10,sK2)) = k5_relat_1(k4_relat_1(sK2),k4_relat_1(X10))) )),
% 2.17/0.70    inference(resolution,[],[f93,f139])).
% 2.17/0.70  fof(f93,plain,(
% 2.17/0.70    ( ! [X0,X1] : (~v1_relat_1(X1) | k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.17/0.70    inference(cnf_transformation,[],[f37])).
% 2.17/0.70  fof(f37,plain,(
% 2.17/0.70    ! [X0] : (! [X1] : (k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.17/0.70    inference(ennf_transformation,[],[f9])).
% 2.17/0.70  fof(f9,axiom,(
% 2.17/0.70    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => k4_relat_1(k5_relat_1(X0,X1)) = k5_relat_1(k4_relat_1(X1),k4_relat_1(X0))))),
% 2.17/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_relat_1)).
% 2.17/0.70  fof(f242,plain,(
% 2.17/0.70    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X1,k6_partfun1(X0))),X0) | ~v1_relat_1(X1)) )),
% 2.17/0.70    inference(subsumption_resolution,[],[f232,f141])).
% 2.17/0.70  fof(f232,plain,(
% 2.17/0.70    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X1,k6_partfun1(X0))),X0) | ~v1_relat_1(k6_partfun1(X0)) | ~v1_relat_1(X1)) )),
% 2.17/0.70    inference(superposition,[],[f92,f125])).
% 2.17/0.70  fof(f92,plain,(
% 2.17/0.70    ( ! [X0,X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 2.17/0.70    inference(cnf_transformation,[],[f36])).
% 2.17/0.70  fof(f36,plain,(
% 2.17/0.70    ! [X0] : (! [X1] : (r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1)) | ~v1_relat_1(X1)) | ~v1_relat_1(X0))),
% 2.17/0.70    inference(ennf_transformation,[],[f8])).
% 2.17/0.70  fof(f8,axiom,(
% 2.17/0.70    ! [X0] : (v1_relat_1(X0) => ! [X1] : (v1_relat_1(X1) => r1_tarski(k2_relat_1(k5_relat_1(X0,X1)),k2_relat_1(X1))))),
% 2.17/0.70    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_relat_1)).
% 2.17/0.70  fof(f1477,plain,(
% 2.17/0.70    ~r1_tarski(k1_relat_1(sK2),sK0) | spl4_24),
% 2.17/0.70    inference(forward_demodulation,[],[f1476,f125])).
% 2.17/0.70  fof(f1476,plain,(
% 2.17/0.70    ~r1_tarski(k1_relat_1(sK2),k2_relat_1(k6_partfun1(sK0))) | spl4_24),
% 2.17/0.70    inference(forward_demodulation,[],[f1464,f123])).
% 2.17/0.70  fof(f1464,plain,(
% 2.17/0.70    ~r1_tarski(k1_relat_1(sK2),k2_relat_1(k4_relat_1(k6_partfun1(sK0)))) | spl4_24),
% 2.17/0.70    inference(backward_demodulation,[],[f796,f1461])).
% 2.17/0.70  fof(f796,plain,(
% 2.17/0.70    ~r1_tarski(k1_relat_1(sK2),k2_relat_1(k4_relat_1(k5_relat_1(sK2,sK3)))) | spl4_24),
% 2.17/0.70    inference(avatar_component_clause,[],[f794])).
% 2.17/0.70  fof(f794,plain,(
% 2.17/0.70    spl4_24 <=> r1_tarski(k1_relat_1(sK2),k2_relat_1(k4_relat_1(k5_relat_1(sK2,sK3))))),
% 2.17/0.70    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 2.17/0.70  fof(f801,plain,(
% 2.17/0.70    ~spl4_24 | spl4_25 | ~spl4_7 | ~spl4_18),
% 2.17/0.70    inference(avatar_split_clause,[],[f789,f671,f291,f798,f794])).
% 2.17/0.70  fof(f671,plain,(
% 2.17/0.70    spl4_18 <=> v1_relat_1(k4_relat_1(sK3))),
% 2.17/0.70    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 2.17/0.70  fof(f789,plain,(
% 2.17/0.70    k1_relat_1(sK2) = k2_relat_1(k4_relat_1(k5_relat_1(sK2,sK3))) | ~r1_tarski(k1_relat_1(sK2),k2_relat_1(k4_relat_1(k5_relat_1(sK2,sK3)))) | (~spl4_7 | ~spl4_18)),
% 2.17/0.70    inference(resolution,[],[f779,f114])).
% 2.17/0.70  fof(f114,plain,(
% 2.17/0.70    ( ! [X0,X1] : (~r1_tarski(X1,X0) | X0 = X1 | ~r1_tarski(X0,X1)) )),
% 2.17/0.70    inference(cnf_transformation,[],[f70])).
% 2.17/0.70  fof(f70,plain,(
% 2.17/0.70    ! [X0,X1] : ((X0 = X1 | ~r1_tarski(X1,X0) | ~r1_tarski(X0,X1)) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.17/0.70    inference(flattening,[],[f69])).
% 2.17/0.71  fof(f69,plain,(
% 2.17/0.71    ! [X0,X1] : ((X0 = X1 | (~r1_tarski(X1,X0) | ~r1_tarski(X0,X1))) & ((r1_tarski(X1,X0) & r1_tarski(X0,X1)) | X0 != X1))),
% 2.17/0.71    inference(nnf_transformation,[],[f1])).
% 2.17/0.71  fof(f1,axiom,(
% 2.17/0.71    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 2.17/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 2.17/0.71  fof(f779,plain,(
% 2.17/0.71    r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(sK2,sK3))),k1_relat_1(sK2)) | (~spl4_7 | ~spl4_18)),
% 2.17/0.71    inference(subsumption_resolution,[],[f777,f672])).
% 2.17/0.71  fof(f672,plain,(
% 2.17/0.71    v1_relat_1(k4_relat_1(sK3)) | ~spl4_18),
% 2.17/0.71    inference(avatar_component_clause,[],[f671])).
% 2.17/0.71  fof(f777,plain,(
% 2.17/0.71    r1_tarski(k2_relat_1(k4_relat_1(k5_relat_1(sK2,sK3))),k1_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK3)) | ~spl4_7),
% 2.17/0.71    inference(superposition,[],[f323,f773])).
% 2.17/0.71  fof(f773,plain,(
% 2.17/0.71    k4_relat_1(k5_relat_1(sK2,sK3)) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(sK2))),
% 2.17/0.71    inference(resolution,[],[f362,f139])).
% 2.17/0.71  fof(f362,plain,(
% 2.17/0.71    ( ! [X11] : (~v1_relat_1(X11) | k4_relat_1(k5_relat_1(X11,sK3)) = k5_relat_1(k4_relat_1(sK3),k4_relat_1(X11))) )),
% 2.17/0.71    inference(resolution,[],[f93,f140])).
% 2.17/0.71  fof(f323,plain,(
% 2.17/0.71    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k4_relat_1(sK2))),k1_relat_1(sK2)) | ~v1_relat_1(X0)) ) | ~spl4_7),
% 2.17/0.71    inference(subsumption_resolution,[],[f318,f292])).
% 2.17/0.71  fof(f318,plain,(
% 2.17/0.71    ( ! [X0] : (r1_tarski(k2_relat_1(k5_relat_1(X0,k4_relat_1(sK2))),k1_relat_1(sK2)) | ~v1_relat_1(k4_relat_1(sK2)) | ~v1_relat_1(X0)) )),
% 2.17/0.71    inference(superposition,[],[f92,f316])).
% 2.17/0.71  fof(f681,plain,(
% 2.17/0.71    spl4_18),
% 2.17/0.71    inference(avatar_contradiction_clause,[],[f680])).
% 2.17/0.71  fof(f680,plain,(
% 2.17/0.71    $false | spl4_18),
% 2.17/0.71    inference(subsumption_resolution,[],[f679,f140])).
% 2.17/0.71  fof(f679,plain,(
% 2.17/0.71    ~v1_relat_1(sK3) | spl4_18),
% 2.17/0.71    inference(resolution,[],[f673,f89])).
% 2.17/0.71  fof(f89,plain,(
% 2.17/0.71    ( ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 2.17/0.71    inference(cnf_transformation,[],[f33])).
% 2.17/0.71  fof(f33,plain,(
% 2.17/0.71    ! [X0] : (v1_relat_1(k4_relat_1(X0)) | ~v1_relat_1(X0))),
% 2.17/0.71    inference(ennf_transformation,[],[f3])).
% 2.17/0.71  fof(f3,axiom,(
% 2.17/0.71    ! [X0] : (v1_relat_1(X0) => v1_relat_1(k4_relat_1(X0)))),
% 2.17/0.71    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k4_relat_1)).
% 2.17/0.71  fof(f673,plain,(
% 2.17/0.71    ~v1_relat_1(k4_relat_1(sK3)) | spl4_18),
% 2.17/0.71    inference(avatar_component_clause,[],[f671])).
% 2.17/0.71  fof(f307,plain,(
% 2.17/0.71    spl4_7),
% 2.17/0.71    inference(avatar_contradiction_clause,[],[f306])).
% 2.17/0.71  fof(f306,plain,(
% 2.17/0.71    $false | spl4_7),
% 2.17/0.71    inference(subsumption_resolution,[],[f305,f139])).
% 2.17/0.71  fof(f305,plain,(
% 2.17/0.71    ~v1_relat_1(sK2) | spl4_7),
% 2.17/0.71    inference(resolution,[],[f293,f89])).
% 2.17/0.71  fof(f293,plain,(
% 2.17/0.71    ~v1_relat_1(k4_relat_1(sK2)) | spl4_7),
% 2.17/0.71    inference(avatar_component_clause,[],[f291])).
% 2.17/0.71  % SZS output end Proof for theBenchmark
% 2.17/0.71  % (26847)------------------------------
% 2.17/0.71  % (26847)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 2.17/0.71  % (26847)Termination reason: Refutation
% 2.17/0.71  
% 2.17/0.71  % (26847)Memory used [KB]: 12537
% 2.17/0.71  % (26847)Time elapsed: 0.250 s
% 2.17/0.71  % (26847)------------------------------
% 2.17/0.71  % (26847)------------------------------
% 2.77/0.71  % (26840)Success in time 0.354 s
%------------------------------------------------------------------------------
