%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT1022+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:03 EST 2020

% Result     : Theorem 16.39s
% Output     : Refutation 16.39s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 271 expanded)
%              Number of leaves         :   14 (  51 expanded)
%              Depth                    :   21
%              Number of atoms          :  253 (1172 expanded)
%              Number of equality atoms :   84 ( 340 expanded)
%              Maximal formula depth    :    9 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f8249,plain,(
    $false ),
    inference(subsumption_resolution,[],[f8089,f4786])).

fof(f4786,plain,(
    sK1 = k3_xboole_0(sK1,sK0) ),
    inference(resolution,[],[f2537,f2665])).

fof(f2665,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(X0,X1)
      | k3_xboole_0(X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f1680])).

fof(f1680,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = X0
      | ~ r1_tarski(X0,X1) ) ),
    inference(ennf_transformation,[],[f86])).

fof(f86,axiom,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
     => k3_xboole_0(X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

fof(f2537,plain,(
    r1_tarski(sK1,sK0) ),
    inference(cnf_transformation,[],[f1582])).

fof(f1582,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f1581])).

fof(f1581,plain,(
    ? [X0,X1,X2] :
      ( ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) != X1
        | k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) != X1 )
      & r1_tarski(X1,X0)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v3_funct_2(X2,X0,X0)
      & v1_funct_2(X2,X0,X0)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f1567])).

fof(f1567,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
          & v3_funct_2(X2,X0,X0)
          & v1_funct_2(X2,X0,X0)
          & v1_funct_1(X2) )
       => ( r1_tarski(X1,X0)
         => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
            & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    inference(negated_conjecture,[],[f1566])).

fof(f1566,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v3_funct_2(X2,X0,X0)
        & v1_funct_2(X2,X0,X0)
        & v1_funct_1(X2) )
     => ( r1_tarski(X1,X0)
       => ( k8_relset_1(X0,X0,X2,k7_relset_1(X0,X0,X2,X1)) = X1
          & k7_relset_1(X0,X0,X2,k8_relset_1(X0,X0,X2,X1)) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_funct_2)).

fof(f8089,plain,(
    sK1 != k3_xboole_0(sK1,sK0) ),
    inference(backward_demodulation,[],[f6327,f8011])).

fof(f8011,plain,(
    sK0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f8010,f5562])).

fof(f5562,plain,(
    v5_relat_1(sK2,sK0) ),
    inference(resolution,[],[f2536,f3988])).

fof(f3988,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f2497])).

fof(f2497,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1211])).

fof(f1211,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f2536,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    inference(cnf_transformation,[],[f1582])).

fof(f8010,plain,
    ( ~ v5_relat_1(sK2,sK0)
    | sK0 = k2_relat_1(sK2) ),
    inference(subsumption_resolution,[],[f8005,f5416])).

fof(f5416,plain,(
    v1_relat_1(sK2) ),
    inference(resolution,[],[f2536,f2689])).

fof(f2689,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f1694])).

fof(f1694,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1210])).

fof(f1210,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f8005,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v5_relat_1(sK2,sK0)
    | sK0 = k2_relat_1(sK2) ),
    inference(resolution,[],[f5339,f3904])).

fof(f3904,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f2434])).

fof(f2434,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2433])).

fof(f2433,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f1477])).

fof(f1477,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_funct_2)).

fof(f5339,plain,(
    v2_funct_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f5338,f2533])).

fof(f2533,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f1582])).

fof(f5338,plain,
    ( ~ v1_funct_1(sK2)
    | v2_funct_2(sK2,sK0) ),
    inference(subsumption_resolution,[],[f5292,f2536])).

fof(f5292,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | v2_funct_2(sK2,sK0) ),
    inference(resolution,[],[f2535,f2799])).

fof(f2799,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_2(X2,X1) ) ),
    inference(cnf_transformation,[],[f1745])).

fof(f1745,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f1744])).

fof(f1744,plain,(
    ! [X0,X1,X2] :
      ( ( v2_funct_2(X2,X1)
        & v2_funct_1(X2)
        & v1_funct_1(X2) )
      | ~ v3_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1470])).

fof(f1470,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( ( v3_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v2_funct_2(X2,X1)
          & v2_funct_1(X2)
          & v1_funct_1(X2) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_funct_2)).

fof(f2535,plain,(
    v3_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f1582])).

fof(f6327,plain,(
    sK1 != k3_xboole_0(sK1,k2_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f6326,f2537])).

fof(f6326,plain,
    ( ~ r1_tarski(sK1,sK0)
    | sK1 != k3_xboole_0(sK1,k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f6325,f5994])).

fof(f5994,plain,(
    sK0 = k1_relat_1(sK2) ),
    inference(forward_demodulation,[],[f5523,f5093])).

fof(f5093,plain,(
    sK0 = k1_relset_1(sK0,sK0,sK2) ),
    inference(subsumption_resolution,[],[f5092,f2536])).

fof(f5092,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k1_relset_1(sK0,sK0,sK2) ),
    inference(subsumption_resolution,[],[f4884,f2533])).

fof(f4884,plain,
    ( ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | sK0 = k1_relset_1(sK0,sK0,sK2) ),
    inference(resolution,[],[f2534,f3399])).

fof(f3399,plain,(
    ! [X0,X1] :
      ( ~ v1_funct_1(X1)
      | ~ v1_funct_2(X1,X0,X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | k1_relset_1(X0,X0,X1) = X0 ) ),
    inference(cnf_transformation,[],[f2124])).

fof(f2124,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(flattening,[],[f2123])).

fof(f2123,plain,(
    ! [X0,X1] :
      ( k1_relset_1(X0,X0,X1) = X0
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      | ~ v1_funct_2(X1,X0,X0)
      | ~ v1_funct_1(X1) ) ),
    inference(ennf_transformation,[],[f1553])).

fof(f1553,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
        & v1_funct_2(X1,X0,X0)
        & v1_funct_1(X1) )
     => k1_relset_1(X0,X0,X1) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_funct_2)).

fof(f2534,plain,(
    v1_funct_2(sK2,sK0,sK0) ),
    inference(cnf_transformation,[],[f1582])).

fof(f5523,plain,(
    k1_relat_1(sK2) = k1_relset_1(sK0,sK0,sK2) ),
    inference(resolution,[],[f2536,f3398])).

fof(f3398,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2122])).

fof(f2122,plain,(
    ! [X0,X1,X2] :
      ( k1_relat_1(X2) = k1_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1227])).

fof(f1227,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relat_1(X2) = k1_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f6325,plain,
    ( sK1 != k3_xboole_0(sK1,k2_relat_1(sK2))
    | ~ r1_tarski(sK1,k1_relat_1(sK2)) ),
    inference(subsumption_resolution,[],[f6324,f5337])).

fof(f5337,plain,(
    v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f5336,f2533])).

fof(f5336,plain,
    ( ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f5291,f2536])).

fof(f5291,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ v1_funct_1(sK2)
    | v2_funct_1(sK2) ),
    inference(resolution,[],[f2535,f2798])).

fof(f2798,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v3_funct_2(X2,X0,X1)
      | v2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f1745])).

fof(f6324,plain,
    ( sK1 != k3_xboole_0(sK1,k2_relat_1(sK2))
    | ~ r1_tarski(sK1,k1_relat_1(sK2))
    | ~ v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f6323,f2533])).

fof(f6323,plain,
    ( sK1 != k3_xboole_0(sK1,k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(sK1,k1_relat_1(sK2))
    | ~ v2_funct_1(sK2) ),
    inference(subsumption_resolution,[],[f6313,f5416])).

fof(f6313,plain,
    ( sK1 != k3_xboole_0(sK1,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(sK1,k1_relat_1(sK2))
    | ~ v2_funct_1(sK2) ),
    inference(trivial_inequality_removal,[],[f6307])).

fof(f6307,plain,
    ( sK1 != sK1
    | sK1 != k3_xboole_0(sK1,k2_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ r1_tarski(sK1,k1_relat_1(sK2))
    | ~ v2_funct_1(sK2) ),
    inference(superposition,[],[f6198,f3327])).

fof(f3327,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v2_funct_1(X1)
      | k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ),
    inference(cnf_transformation,[],[f2053])).

fof(f2053,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2052])).

fof(f2052,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,k9_relat_1(X1,X0)) = X0
      | ~ v2_funct_1(X1)
      | ~ r1_tarski(X0,k1_relat_1(X1))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f985])).

fof(f985,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( ( v2_funct_1(X1)
          & r1_tarski(X0,k1_relat_1(X1)) )
       => k10_relat_1(X1,k9_relat_1(X1,X0)) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t164_funct_1)).

fof(f6198,plain,
    ( sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    | sK1 != k3_xboole_0(sK1,k2_relat_1(sK2)) ),
    inference(backward_demodulation,[],[f5805,f6195])).

fof(f6195,plain,(
    ! [X578] : k9_relat_1(sK2,k10_relat_1(sK2,X578)) = k3_xboole_0(X578,k2_relat_1(sK2)) ),
    inference(forward_demodulation,[],[f6194,f5941])).

fof(f5941,plain,(
    k2_relat_1(sK2) = k9_relat_1(sK2,sK0) ),
    inference(backward_demodulation,[],[f5748,f5509])).

fof(f5509,plain,(
    k2_relat_1(sK2) = k2_relset_1(sK0,sK0,sK2) ),
    inference(resolution,[],[f2536,f3380])).

fof(f3380,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f2112])).

fof(f2112,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1228])).

fof(f1228,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f5748,plain,(
    k2_relset_1(sK0,sK0,sK2) = k9_relat_1(sK2,sK0) ),
    inference(forward_demodulation,[],[f5392,f5386])).

fof(f5386,plain,(
    ! [X42] : k7_relset_1(sK0,sK0,sK2,X42) = k9_relat_1(sK2,X42) ),
    inference(resolution,[],[f2536,f2550])).

fof(f2550,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f1594])).

fof(f1594,plain,(
    ! [X0,X1,X2,X3] :
      ( k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1233])).

fof(f1233,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k7_relset_1(X0,X1,X2,X3) = k9_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k7_relset_1)).

fof(f5392,plain,(
    k2_relset_1(sK0,sK0,sK2) = k7_relset_1(sK0,sK0,sK2,sK0) ),
    inference(resolution,[],[f2536,f2559])).

fof(f2559,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ),
    inference(cnf_transformation,[],[f1603])).

fof(f1603,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1258])).

fof(f1258,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f6194,plain,(
    ! [X578] : k9_relat_1(sK2,k10_relat_1(sK2,X578)) = k3_xboole_0(X578,k9_relat_1(sK2,sK0)) ),
    inference(subsumption_resolution,[],[f6067,f5416])).

fof(f6067,plain,(
    ! [X578] :
      ( k9_relat_1(sK2,k10_relat_1(sK2,X578)) = k3_xboole_0(X578,k9_relat_1(sK2,sK0))
      | ~ v1_relat_1(sK2) ) ),
    inference(backward_demodulation,[],[f4481,f5994])).

fof(f4481,plain,(
    ! [X578] :
      ( ~ v1_relat_1(sK2)
      | k9_relat_1(sK2,k10_relat_1(sK2,X578)) = k3_xboole_0(X578,k9_relat_1(sK2,k1_relat_1(sK2))) ) ),
    inference(resolution,[],[f2533,f3332])).

fof(f3332,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    inference(cnf_transformation,[],[f2063])).

fof(f2063,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f2062])).

fof(f2062,plain,(
    ! [X0,X1] :
      ( k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1)))
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f967])).

fof(f967,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => k9_relat_1(X1,k10_relat_1(X1,X0)) = k3_xboole_0(X0,k9_relat_1(X1,k1_relat_1(X1))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_funct_1)).

fof(f5805,plain,
    ( sK1 != k9_relat_1(sK2,k10_relat_1(sK2,sK1))
    | sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1)) ),
    inference(forward_demodulation,[],[f5804,f5402])).

fof(f5402,plain,(
    ! [X60] : k8_relset_1(sK0,sK0,sK2,X60) = k10_relat_1(sK2,X60) ),
    inference(resolution,[],[f2536,f2569])).

fof(f2569,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f1609])).

fof(f1609,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1234])).

fof(f1234,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f5804,plain,
    ( sK1 != k10_relat_1(sK2,k9_relat_1(sK2,sK1))
    | sK1 != k9_relat_1(sK2,k8_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(backward_demodulation,[],[f5738,f5402])).

fof(f5738,plain,
    ( sK1 != k8_relset_1(sK0,sK0,sK2,k9_relat_1(sK2,sK1))
    | sK1 != k9_relat_1(sK2,k8_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(forward_demodulation,[],[f5736,f5386])).

fof(f5736,plain,
    ( sK1 != k9_relat_1(sK2,k8_relset_1(sK0,sK0,sK2,sK1))
    | sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(backward_demodulation,[],[f2532,f5386])).

fof(f2532,plain,
    ( sK1 != k7_relset_1(sK0,sK0,sK2,k8_relset_1(sK0,sK0,sK2,sK1))
    | sK1 != k8_relset_1(sK0,sK0,sK2,k7_relset_1(sK0,sK0,sK2,sK1)) ),
    inference(cnf_transformation,[],[f1582])).
%------------------------------------------------------------------------------
