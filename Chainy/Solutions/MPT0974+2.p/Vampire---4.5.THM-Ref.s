%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0974+2 : TPTP v7.4.0. Released v7.4.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Wed Dec 16 12:10:00 EST 2020

% Result     : Theorem 16.21s
% Output     : Refutation 16.21s
% Verified   : 
% Statistics : Number of formulae       :  103 ( 179 expanded)
%              Number of leaves         :   27 (  77 expanded)
%              Depth                    :    9
%              Number of atoms          :  306 ( 651 expanded)
%              Number of equality atoms :   50 ( 166 expanded)
%              Maximal formula depth    :   13 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f6029,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f2491,f2501,f2506,f2516,f2521,f2526,f2536,f2625,f2662,f2677,f2747,f2762,f2806,f2809,f3073,f5700,f5752,f5996,f6027])).

fof(f6027,plain,
    ( ~ spl121_41
    | ~ spl121_38
    | spl121_556 ),
    inference(avatar_split_clause,[],[f6024,f5993,f2729,f2744])).

fof(f2744,plain,
    ( spl121_41
  <=> v4_relat_1(sK4,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_41])])).

fof(f2729,plain,
    ( spl121_38
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_38])])).

fof(f5993,plain,
    ( spl121_556
  <=> r1_tarski(k1_relat_1(sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_556])])).

fof(f6024,plain,
    ( ~ v1_relat_1(sK4)
    | ~ v4_relat_1(sK4,sK1)
    | spl121_556 ),
    inference(resolution,[],[f5995,f2430])).

fof(f2430,plain,(
    ! [X0,X1] :
      ( r1_tarski(k1_relat_1(X1),X0)
      | ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f1792])).

fof(f1792,plain,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f651])).

fof(f651,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( v4_relat_1(X1,X0)
      <=> r1_tarski(k1_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d18_relat_1)).

fof(f5995,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),sK1)
    | spl121_556 ),
    inference(avatar_component_clause,[],[f5993])).

fof(f5996,plain,
    ( ~ spl121_38
    | ~ spl121_17
    | ~ spl121_556
    | ~ spl121_30
    | ~ spl121_32
    | spl121_326 ),
    inference(avatar_split_clause,[],[f5991,f4534,f2673,f2658,f5993,f2591,f2729])).

fof(f2591,plain,
    ( spl121_17
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_17])])).

fof(f2658,plain,
    ( spl121_30
  <=> sK2 = k2_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_30])])).

fof(f2673,plain,
    ( spl121_32
  <=> sK1 = k2_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_32])])).

fof(f4534,plain,
    ( spl121_326
  <=> sK2 = k2_relat_1(k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_326])])).

fof(f5991,plain,
    ( ~ r1_tarski(k1_relat_1(sK4),sK1)
    | ~ v1_relat_1(sK3)
    | ~ v1_relat_1(sK4)
    | ~ spl121_30
    | ~ spl121_32
    | spl121_326 ),
    inference(forward_demodulation,[],[f5990,f2675])).

fof(f2675,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ spl121_32 ),
    inference(avatar_component_clause,[],[f2673])).

fof(f5990,plain,
    ( ~ v1_relat_1(sK3)
    | ~ r1_tarski(k1_relat_1(sK4),k2_relat_1(sK3))
    | ~ v1_relat_1(sK4)
    | ~ spl121_30
    | spl121_326 ),
    inference(trivial_inequality_removal,[],[f5989])).

fof(f5989,plain,
    ( sK2 != sK2
    | ~ v1_relat_1(sK3)
    | ~ r1_tarski(k1_relat_1(sK4),k2_relat_1(sK3))
    | ~ v1_relat_1(sK4)
    | ~ spl121_30
    | spl121_326 ),
    inference(forward_demodulation,[],[f5985,f2660])).

fof(f2660,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ spl121_30 ),
    inference(avatar_component_clause,[],[f2658])).

fof(f5985,plain,
    ( sK2 != k2_relat_1(sK4)
    | ~ v1_relat_1(sK3)
    | ~ r1_tarski(k1_relat_1(sK4),k2_relat_1(sK3))
    | ~ v1_relat_1(sK4)
    | spl121_326 ),
    inference(superposition,[],[f4536,f1934])).

fof(f1934,plain,(
    ! [X0,X1] :
      ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
      | ~ v1_relat_1(X1)
      | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f1604])).

fof(f1604,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f1603])).

fof(f1603,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f846])).

fof(f846,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_relat_1)).

fof(f4536,plain,
    ( sK2 != k2_relat_1(k5_relat_1(sK3,sK4))
    | spl121_326 ),
    inference(avatar_component_clause,[],[f4534])).

fof(f5752,plain,
    ( ~ spl121_3
    | ~ spl121_8
    | ~ spl121_10
    | ~ spl121_1
    | ~ spl121_326
    | spl121_53 ),
    inference(avatar_split_clause,[],[f5750,f2803,f4534,f2488,f2533,f2523,f2498])).

fof(f2498,plain,
    ( spl121_3
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_3])])).

fof(f2523,plain,
    ( spl121_8
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_8])])).

fof(f2533,plain,
    ( spl121_10
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_10])])).

fof(f2488,plain,
    ( spl121_1
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_1])])).

fof(f2803,plain,
    ( spl121_53
  <=> sK2 = k2_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_53])])).

fof(f5750,plain,
    ( sK2 != k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3)
    | spl121_53 ),
    inference(superposition,[],[f2805,f1805])).

fof(f1805,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f1507])).

fof(f1507,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f1506])).

fof(f1506,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f1480])).

fof(f1480,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k5_relat_1(X4,X5) = k1_partfun1(X0,X1,X2,X3,X4,X5) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f2805,plain,
    ( sK2 != k2_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    | spl121_53 ),
    inference(avatar_component_clause,[],[f2803])).

fof(f5700,plain,
    ( ~ spl121_3
    | ~ spl121_8
    | ~ spl121_10
    | ~ spl121_1
    | spl121_52 ),
    inference(avatar_split_clause,[],[f5687,f2799,f2488,f2533,f2523,f2498])).

fof(f2799,plain,
    ( spl121_52
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_52])])).

fof(f5687,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ v1_funct_1(sK3)
    | spl121_52 ),
    inference(resolution,[],[f2801,f1804])).

fof(f1804,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f1505])).

fof(f1505,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f1504])).

fof(f1504,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f1474])).

fof(f1474,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f2801,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl121_52 ),
    inference(avatar_component_clause,[],[f2799])).

fof(f3073,plain,(
    spl121_44 ),
    inference(avatar_contradiction_clause,[],[f3071])).

fof(f3071,plain,
    ( $false
    | spl121_44 ),
    inference(resolution,[],[f2761,f1878])).

fof(f1878,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f696])).

fof(f696,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f2761,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | spl121_44 ),
    inference(avatar_component_clause,[],[f2759])).

fof(f2759,plain,
    ( spl121_44
  <=> v1_relat_1(k2_zfmisc_1(sK1,sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_44])])).

fof(f2809,plain,(
    spl121_23 ),
    inference(avatar_contradiction_clause,[],[f2807])).

fof(f2807,plain,
    ( $false
    | spl121_23 ),
    inference(resolution,[],[f2624,f1878])).

fof(f2624,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | spl121_23 ),
    inference(avatar_component_clause,[],[f2622])).

fof(f2622,plain,
    ( spl121_23
  <=> v1_relat_1(k2_zfmisc_1(sK0,sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_23])])).

fof(f2806,plain,
    ( ~ spl121_52
    | ~ spl121_53
    | spl121_4 ),
    inference(avatar_split_clause,[],[f2792,f2503,f2803,f2799])).

fof(f2503,plain,
    ( spl121_4
  <=> sK2 = k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_4])])).

fof(f2792,plain,
    ( sK2 != k2_relat_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | spl121_4 ),
    inference(superposition,[],[f2505,f1825])).

fof(f1825,plain,(
    ! [X2,X0,X1] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f1522])).

fof(f1522,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f1228])).

fof(f1228,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f2505,plain,
    ( sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4))
    | spl121_4 ),
    inference(avatar_component_clause,[],[f2503])).

fof(f2762,plain,
    ( spl121_38
    | ~ spl121_44
    | ~ spl121_8 ),
    inference(avatar_split_clause,[],[f2700,f2523,f2759,f2729])).

fof(f2700,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK1,sK2))
    | v1_relat_1(sK4)
    | ~ spl121_8 ),
    inference(resolution,[],[f2525,f1853])).

fof(f1853,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0)
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f1539])).

fof(f1539,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f639])).

fof(f639,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f2525,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl121_8 ),
    inference(avatar_component_clause,[],[f2523])).

fof(f2747,plain,
    ( spl121_41
    | ~ spl121_8 ),
    inference(avatar_split_clause,[],[f2695,f2523,f2744])).

fof(f2695,plain,
    ( v4_relat_1(sK4,sK1)
    | ~ spl121_8 ),
    inference(resolution,[],[f2525,f2400])).

fof(f2400,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f1781])).

fof(f1781,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f2677,plain,
    ( ~ spl121_1
    | spl121_32
    | ~ spl121_7 ),
    inference(avatar_split_clause,[],[f2669,f2518,f2673,f2488])).

fof(f2518,plain,
    ( spl121_7
  <=> sK1 = k2_relset_1(sK0,sK1,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_7])])).

fof(f2669,plain,
    ( sK1 = k2_relat_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl121_7 ),
    inference(superposition,[],[f1825,f2520])).

fof(f2520,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK3)
    | ~ spl121_7 ),
    inference(avatar_component_clause,[],[f2518])).

fof(f2662,plain,
    ( ~ spl121_8
    | spl121_30
    | ~ spl121_6 ),
    inference(avatar_split_clause,[],[f2654,f2513,f2658,f2523])).

fof(f2513,plain,
    ( spl121_6
  <=> sK2 = k2_relset_1(sK1,sK2,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl121_6])])).

fof(f2654,plain,
    ( sK2 = k2_relat_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl121_6 ),
    inference(superposition,[],[f1825,f2515])).

fof(f2515,plain,
    ( sK2 = k2_relset_1(sK1,sK2,sK4)
    | ~ spl121_6 ),
    inference(avatar_component_clause,[],[f2513])).

fof(f2625,plain,
    ( spl121_17
    | ~ spl121_23
    | ~ spl121_1 ),
    inference(avatar_split_clause,[],[f2554,f2488,f2622,f2591])).

fof(f2554,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | v1_relat_1(sK3)
    | ~ spl121_1 ),
    inference(resolution,[],[f2490,f1853])).

fof(f2490,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl121_1 ),
    inference(avatar_component_clause,[],[f2488])).

fof(f2536,plain,(
    spl121_10 ),
    inference(avatar_split_clause,[],[f1793,f2533])).

fof(f1793,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f1503])).

fof(f1503,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          & k1_xboole_0 != X2
          & k2_relset_1(X1,X2,X4) = X2
          & k2_relset_1(X0,X1,X3) = X1
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(flattening,[],[f1502])).

fof(f1502,plain,(
    ? [X0,X1,X2,X3] :
      ( ? [X4] :
          ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) != X2
          & k1_xboole_0 != X2
          & k2_relset_1(X1,X2,X4) = X2
          & k2_relset_1(X0,X1,X3) = X1
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
          & v1_funct_2(X4,X1,X2)
          & v1_funct_1(X4) )
      & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X3,X0,X1)
      & v1_funct_1(X3) ) ),
    inference(ennf_transformation,[],[f1488])).

fof(f1488,negated_conjecture,(
    ~ ! [X0,X1,X2,X3] :
        ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X3,X0,X1)
          & v1_funct_1(X3) )
       => ! [X4] :
            ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
              & v1_funct_2(X4,X1,X2)
              & v1_funct_1(X4) )
           => ( ( k2_relset_1(X1,X2,X4) = X2
                & k2_relset_1(X0,X1,X3) = X1 )
             => ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
                | k1_xboole_0 = X2 ) ) ) ) ),
    inference(negated_conjecture,[],[f1487])).

fof(f1487,conjecture,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3) )
     => ! [X4] :
          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
            & v1_funct_2(X4,X1,X2)
            & v1_funct_1(X4) )
         => ( ( k2_relset_1(X1,X2,X4) = X2
              & k2_relset_1(X0,X1,X3) = X1 )
           => ( k2_relset_1(X0,X2,k1_partfun1(X0,X1,X1,X2,X3,X4)) = X2
              | k1_xboole_0 = X2 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_funct_2)).

fof(f2526,plain,(
    spl121_8 ),
    inference(avatar_split_clause,[],[f1795,f2523])).

fof(f1795,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f1503])).

fof(f2521,plain,(
    spl121_7 ),
    inference(avatar_split_clause,[],[f1796,f2518])).

fof(f1796,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK3) ),
    inference(cnf_transformation,[],[f1503])).

fof(f2516,plain,(
    spl121_6 ),
    inference(avatar_split_clause,[],[f1797,f2513])).

fof(f1797,plain,(
    sK2 = k2_relset_1(sK1,sK2,sK4) ),
    inference(cnf_transformation,[],[f1503])).

fof(f2506,plain,(
    ~ spl121_4 ),
    inference(avatar_split_clause,[],[f1799,f2503])).

fof(f1799,plain,(
    sK2 != k2_relset_1(sK0,sK2,k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4)) ),
    inference(cnf_transformation,[],[f1503])).

fof(f2501,plain,(
    spl121_3 ),
    inference(avatar_split_clause,[],[f1800,f2498])).

fof(f1800,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f1503])).

fof(f2491,plain,(
    spl121_1 ),
    inference(avatar_split_clause,[],[f1802,f2488])).

fof(f1802,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f1503])).
%------------------------------------------------------------------------------
