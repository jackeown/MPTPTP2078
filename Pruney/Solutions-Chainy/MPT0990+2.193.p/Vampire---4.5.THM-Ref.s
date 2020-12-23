%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:03:02 EST 2020

% Result     : Theorem 0.22s
% Output     : Refutation 1.47s
% Verified   : 
% Statistics : Number of formulae       :  260 ( 585 expanded)
%              Number of leaves         :   49 ( 246 expanded)
%              Depth                    :   16
%              Number of atoms          : 1219 (2925 expanded)
%              Number of equality atoms :  237 ( 755 expanded)
%              Maximal formula depth    :   16 (   6 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f787,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f88,f93,f98,f103,f108,f113,f118,f123,f128,f133,f138,f143,f149,f159,f165,f202,f225,f241,f253,f277,f292,f318,f355,f405,f428,f437,f459,f494,f519,f552,f633,f786])).

fof(f786,plain,
    ( spl4_46
    | ~ spl4_57 ),
    inference(avatar_contradiction_clause,[],[f785])).

fof(f785,plain,
    ( $false
    | spl4_46
    | ~ spl4_57 ),
    inference(subsumption_resolution,[],[f784,f493])).

fof(f493,plain,
    ( sK1 != k1_relat_1(sK3)
    | spl4_46 ),
    inference(avatar_component_clause,[],[f491])).

fof(f491,plain,
    ( spl4_46
  <=> sK1 = k1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).

fof(f784,plain,
    ( sK1 = k1_relat_1(sK3)
    | ~ spl4_57 ),
    inference(forward_demodulation,[],[f775,f77])).

fof(f77,plain,(
    ! [X0] : k2_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).

fof(f775,plain,
    ( k1_relat_1(sK3) = k2_relat_1(k6_relat_1(sK1))
    | ~ spl4_57 ),
    inference(superposition,[],[f77,f628])).

fof(f628,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3))
    | ~ spl4_57 ),
    inference(avatar_component_clause,[],[f626])).

fof(f626,plain,
    ( spl4_57
  <=> k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).

fof(f633,plain,
    ( spl4_57
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_27
    | ~ spl4_28 ),
    inference(avatar_split_clause,[],[f632,f315,f306,f156,f125,f626])).

fof(f125,plain,
    ( spl4_9
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).

fof(f156,plain,
    ( spl4_14
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).

fof(f306,plain,
    ( spl4_27
  <=> v2_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).

fof(f315,plain,
    ( spl4_28
  <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).

fof(f632,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3))
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_27
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f631,f158])).

fof(f158,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_14 ),
    inference(avatar_component_clause,[],[f156])).

fof(f631,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3))
    | ~ v1_relat_1(sK3)
    | ~ spl4_9
    | ~ spl4_27
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f630,f127])).

fof(f127,plain,
    ( v1_funct_1(sK3)
    | ~ spl4_9 ),
    inference(avatar_component_clause,[],[f125])).

fof(f630,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3))
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_27
    | ~ spl4_28 ),
    inference(subsumption_resolution,[],[f617,f307])).

fof(f307,plain,
    ( v2_funct_1(sK3)
    | ~ spl4_27 ),
    inference(avatar_component_clause,[],[f306])).

fof(f617,plain,
    ( k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3))
    | ~ v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ spl4_28 ),
    inference(superposition,[],[f59,f317])).

fof(f317,plain,
    ( k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ spl4_28 ),
    inference(avatar_component_clause,[],[f315])).

fof(f59,plain,(
    ! [X0] :
      ( k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f552,plain,
    ( spl4_27
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_41 ),
    inference(avatar_split_clause,[],[f551,f425,f140,f135,f130,f125,f120,f115,f110,f95,f306])).

fof(f95,plain,
    ( spl4_3
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).

fof(f110,plain,
    ( spl4_6
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).

fof(f115,plain,
    ( spl4_7
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).

fof(f120,plain,
    ( spl4_8
  <=> v1_funct_2(sK3,sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).

fof(f130,plain,
    ( spl4_10
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).

fof(f135,plain,
    ( spl4_11
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).

fof(f140,plain,
    ( spl4_12
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).

fof(f425,plain,
    ( spl4_41
  <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).

fof(f551,plain,
    ( v2_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f550,f127])).

fof(f550,plain,
    ( v2_funct_1(sK3)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f549,f122])).

fof(f122,plain,
    ( v1_funct_2(sK3,sK1,sK0)
    | ~ spl4_8 ),
    inference(avatar_component_clause,[],[f120])).

fof(f549,plain,
    ( v2_funct_1(sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f548,f117])).

fof(f117,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl4_7 ),
    inference(avatar_component_clause,[],[f115])).

fof(f548,plain,
    ( v2_funct_1(sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f537,f97])).

fof(f97,plain,
    ( k1_xboole_0 != sK0
    | spl4_3 ),
    inference(avatar_component_clause,[],[f95])).

fof(f537,plain,
    ( v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_41 ),
    inference(subsumption_resolution,[],[f529,f67])).

fof(f67,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f529,plain,
    ( ~ v2_funct_1(k6_relat_1(sK0))
    | v2_funct_1(sK3)
    | k1_xboole_0 = sK0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_41 ),
    inference(superposition,[],[f336,f427])).

fof(f427,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ spl4_41 ),
    inference(avatar_component_clause,[],[f425])).

fof(f336,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | v2_funct_1(X1)
        | k1_xboole_0 = X0
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1) )
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f335,f142])).

fof(f142,plain,
    ( v1_funct_1(sK2)
    | ~ spl4_12 ),
    inference(avatar_component_clause,[],[f140])).

fof(f335,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f334,f137])).

fof(f137,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl4_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f334,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f333,f132])).

fof(f132,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl4_10 ),
    inference(avatar_component_clause,[],[f130])).

fof(f333,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f330])).

fof(f330,plain,
    ( ! [X0,X1] :
        ( sK1 != sK1
        | k1_xboole_0 = X0
        | v2_funct_1(X1)
        | ~ v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0)))
        | ~ v1_funct_2(X1,sK1,X0)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
        | ~ v1_funct_2(sK2,sK0,sK1)
        | ~ v1_funct_1(sK2) )
    | ~ spl4_6 ),
    inference(superposition,[],[f63,f112])).

fof(f112,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl4_6 ),
    inference(avatar_component_clause,[],[f110])).

fof(f63,plain,(
    ! [X4,X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X3) != X1
      | k1_xboole_0 = X2
      | v2_funct_1(X4)
      | ~ v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X4,X1,X2)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
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
    inference(flattening,[],[f27])).

fof(f27,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f519,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_40 ),
    inference(avatar_contradiction_clause,[],[f518])).

fof(f518,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_40 ),
    inference(subsumption_resolution,[],[f517,f142])).

fof(f517,plain,
    ( ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | spl4_40 ),
    inference(subsumption_resolution,[],[f516,f132])).

fof(f516,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | spl4_40 ),
    inference(subsumption_resolution,[],[f515,f127])).

fof(f515,plain,
    ( ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | spl4_40 ),
    inference(subsumption_resolution,[],[f512,f117])).

fof(f512,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | spl4_40 ),
    inference(resolution,[],[f423,f74])).

fof(f74,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).

fof(f423,plain,
    ( ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_40 ),
    inference(avatar_component_clause,[],[f421])).

fof(f421,plain,
    ( spl4_40
  <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).

fof(f494,plain,
    ( ~ spl4_46
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_24
    | ~ spl4_37
    | ~ spl4_43 ),
    inference(avatar_split_clause,[],[f489,f434,f400,f272,f162,f156,f140,f125,f85,f491])).

fof(f85,plain,
    ( spl4_1
  <=> k2_funct_1(sK2) = sK3 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).

fof(f162,plain,
    ( spl4_15
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).

fof(f272,plain,
    ( spl4_24
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).

fof(f400,plain,
    ( spl4_37
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).

fof(f434,plain,
    ( spl4_43
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).

fof(f489,plain,
    ( sK1 != k1_relat_1(sK3)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_24
    | ~ spl4_37
    | ~ spl4_43 ),
    inference(forward_demodulation,[],[f488,f402])).

fof(f402,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_37 ),
    inference(avatar_component_clause,[],[f400])).

fof(f488,plain,
    ( k2_relat_1(sK2) != k1_relat_1(sK3)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_24
    | ~ spl4_43 ),
    inference(trivial_inequality_removal,[],[f487])).

fof(f487,plain,
    ( k6_relat_1(sK0) != k6_relat_1(sK0)
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_24
    | ~ spl4_43 ),
    inference(forward_demodulation,[],[f486,f274])).

fof(f274,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_24 ),
    inference(avatar_component_clause,[],[f272])).

fof(f486,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_15
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f485,f164])).

fof(f164,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_15 ),
    inference(avatar_component_clause,[],[f162])).

fof(f485,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_12
    | ~ spl4_14
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f484,f142])).

fof(f484,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_14
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f483,f158])).

fof(f483,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_9
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f482,f127])).

fof(f482,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl4_1
    | ~ spl4_43 ),
    inference(subsumption_resolution,[],[f478,f87])).

fof(f87,plain,
    ( k2_funct_1(sK2) != sK3
    | spl4_1 ),
    inference(avatar_component_clause,[],[f85])).

fof(f478,plain,
    ( k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2))
    | k2_funct_1(sK2) = sK3
    | k2_relat_1(sK2) != k1_relat_1(sK3)
    | ~ v1_funct_1(sK3)
    | ~ v1_relat_1(sK3)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_43 ),
    inference(superposition,[],[f186,f436])).

fof(f436,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ spl4_43 ),
    inference(avatar_component_clause,[],[f434])).

fof(f186,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(subsumption_resolution,[],[f58,f65])).

fof(f65,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( v2_funct_1(X0)
      | ! [X1] :
          ( k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( ? [X1] :
            ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
            & v1_funct_1(X1)
            & v1_relat_1(X1) )
       => v2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).

fof(f58,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
      | k2_relat_1(X0) != k1_relat_1(X1)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0))
          | k2_relat_1(X0) != k1_relat_1(X1)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0))
              & k2_relat_1(X0) = k1_relat_1(X1)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).

fof(f459,plain,
    ( ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_42 ),
    inference(avatar_contradiction_clause,[],[f445])).

fof(f445,plain,
    ( $false
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | spl4_42 ),
    inference(unit_resulting_resolution,[],[f142,f127,f132,f117,f432,f208])).

fof(f208,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(duplicate_literal_removal,[],[f207])).

fof(f207,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(superposition,[],[f74,f75])).

% (17534)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
fof(f75,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f432,plain,
    ( ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | spl4_42 ),
    inference(avatar_component_clause,[],[f430])).

fof(f430,plain,
    ( spl4_42
  <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).

fof(f437,plain,
    ( ~ spl4_42
    | spl4_43
    | ~ spl4_18 ),
    inference(avatar_split_clause,[],[f417,f199,f434,f430])).

fof(f199,plain,
    ( spl4_18
  <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).

fof(f417,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,sK3)
    | ~ m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_18 ),
    inference(resolution,[],[f185,f201])).

fof(f201,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_18 ),
    inference(avatar_component_clause,[],[f199])).

fof(f185,plain,(
    ! [X2,X3] :
      ( ~ r2_relset_1(X2,X2,X3,k6_relat_1(X2))
      | k6_relat_1(X2) = X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2))) ) ),
    inference(resolution,[],[f68,f150])).

fof(f150,plain,(
    ! [X0] : m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(forward_demodulation,[],[f71,f72])).

fof(f72,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f71,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) ),
    inference(pure_predicate_removal,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))
      & v1_partfun1(k6_partfun1(X0),X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).

fof(f68,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ r2_relset_1(X0,X1,X2,X3)
      | X2 = X3
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_relset_1(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_relset_1(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
     => ( r2_relset_1(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).

fof(f428,plain,
    ( ~ spl4_40
    | spl4_41
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f416,f146,f425,f421])).

fof(f146,plain,
    ( spl4_13
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).

fof(f416,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)
    | ~ m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))
    | ~ spl4_13 ),
    inference(resolution,[],[f185,f148])).

fof(f148,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_13 ),
    inference(avatar_component_clause,[],[f146])).

fof(f405,plain,
    ( spl4_37
    | ~ spl4_30 ),
    inference(avatar_split_clause,[],[f404,f348,f400])).

fof(f348,plain,
    ( spl4_30
  <=> k6_relat_1(k2_relat_1(sK2)) = k6_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).

fof(f404,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl4_30 ),
    inference(forward_demodulation,[],[f394,f77])).

fof(f394,plain,
    ( k2_relat_1(sK2) = k2_relat_1(k6_relat_1(sK1))
    | ~ spl4_30 ),
    inference(superposition,[],[f77,f350])).

fof(f350,plain,
    ( k6_relat_1(k2_relat_1(sK2)) = k6_relat_1(sK1)
    | ~ spl4_30 ),
    inference(avatar_component_clause,[],[f348])).

fof(f355,plain,
    ( spl4_30
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_21 ),
    inference(avatar_split_clause,[],[f354,f250,f162,f140,f100,f348])).

fof(f100,plain,
    ( spl4_4
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).

fof(f250,plain,
    ( spl4_21
  <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).

fof(f354,plain,
    ( k6_relat_1(k2_relat_1(sK2)) = k6_relat_1(sK1)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f353,f164])).

fof(f353,plain,
    ( k6_relat_1(k2_relat_1(sK2)) = k6_relat_1(sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f352,f142])).

fof(f352,plain,
    ( k6_relat_1(k2_relat_1(sK2)) = k6_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_21 ),
    inference(subsumption_resolution,[],[f341,f102])).

fof(f102,plain,
    ( v2_funct_1(sK2)
    | ~ spl4_4 ),
    inference(avatar_component_clause,[],[f100])).

fof(f341,plain,
    ( k6_relat_1(k2_relat_1(sK2)) = k6_relat_1(sK1)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_21 ),
    inference(superposition,[],[f60,f252])).

fof(f252,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ spl4_21 ),
    inference(avatar_component_clause,[],[f250])).

fof(f60,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f318,plain,
    ( spl4_28
    | ~ spl4_27
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_25 ),
    inference(avatar_split_clause,[],[f313,f289,f125,f120,f115,f95,f306,f315])).

fof(f289,plain,
    ( spl4_25
  <=> sK0 = k2_relset_1(sK1,sK0,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).

fof(f313,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f312,f127])).

fof(f312,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f311,f122])).

fof(f311,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_7
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f310,f117])).

fof(f310,plain,
    ( ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | spl4_3
    | ~ spl4_25 ),
    inference(subsumption_resolution,[],[f295,f97])).

fof(f295,plain,
    ( k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_25 ),
    inference(trivial_inequality_removal,[],[f294])).

fof(f294,plain,
    ( sK0 != sK0
    | k1_xboole_0 = sK0
    | ~ v2_funct_1(sK3)
    | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_25 ),
    inference(superposition,[],[f212,f291])).

fof(f291,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_25 ),
    inference(avatar_component_clause,[],[f289])).

fof(f212,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f56,f72])).

fof(f56,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f292,plain,
    ( spl4_25
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f287,f146,f140,f135,f130,f125,f120,f115,f289])).

fof(f287,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f286,f127])).

fof(f286,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_8
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f285,f122])).

fof(f285,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_7
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f284,f117])).

fof(f284,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f283,f142])).

fof(f283,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f282,f137])).

fof(f282,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f279,f132])).

fof(f279,plain,
    ( sK0 = k2_relset_1(sK1,sK0,sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_2(sK3,sK1,sK0)
    | ~ v1_funct_1(sK3)
    | ~ spl4_13 ),
    inference(resolution,[],[f278,f148])).

fof(f278,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1))
      | k2_relset_1(X0,X1,X2) = X1
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f70,f72])).

fof(f70,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(X0,X1,X2) = X1
      | ~ r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X3,X1,X0)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
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

fof(f277,plain,
    ( spl4_24
    | ~ spl4_20 ),
    inference(avatar_split_clause,[],[f276,f234,f272])).

fof(f234,plain,
    ( spl4_20
  <=> k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).

fof(f276,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl4_20 ),
    inference(forward_demodulation,[],[f257,f76])).

fof(f76,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f257,plain,
    ( k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0))
    | ~ spl4_20 ),
    inference(superposition,[],[f76,f236])).

fof(f236,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))
    | ~ spl4_20 ),
    inference(avatar_component_clause,[],[f234])).

fof(f253,plain,
    ( spl4_21
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f248,f140,f135,f130,f110,f100,f90,f250])).

fof(f90,plain,
    ( spl4_2
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).

fof(f248,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f247,f142])).

fof(f247,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f246,f137])).

fof(f246,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f245,f132])).

fof(f245,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f244,f102])).

fof(f244,plain,
    ( ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f243,f92])).

fof(f92,plain,
    ( k1_xboole_0 != sK1
    | spl4_2 ),
    inference(avatar_component_clause,[],[f90])).

fof(f243,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f242])).

fof(f242,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f213,f112])).

fof(f213,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(forward_demodulation,[],[f57,f72])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2)
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f241,plain,
    ( spl4_20
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_19 ),
    inference(avatar_split_clause,[],[f240,f222,f162,f140,f100,f234])).

fof(f222,plain,
    ( spl4_19
  <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).

fof(f240,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_15
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f239,f164])).

fof(f239,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_12
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f238,f142])).

fof(f238,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_4
    | ~ spl4_19 ),
    inference(subsumption_resolution,[],[f227,f102])).

fof(f227,plain,
    ( k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl4_19 ),
    inference(superposition,[],[f59,f224])).

fof(f224,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl4_19 ),
    inference(avatar_component_clause,[],[f222])).

fof(f225,plain,
    ( spl4_19
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(avatar_split_clause,[],[f220,f140,f135,f130,f110,f100,f90,f222])).

fof(f220,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11
    | ~ spl4_12 ),
    inference(subsumption_resolution,[],[f219,f142])).

fof(f219,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10
    | ~ spl4_11 ),
    inference(subsumption_resolution,[],[f218,f137])).

fof(f218,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f217,f132])).

fof(f217,plain,
    ( k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_4
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f216,f102])).

fof(f216,plain,
    ( ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | spl4_2
    | ~ spl4_6 ),
    inference(subsumption_resolution,[],[f215,f92])).

fof(f215,plain,
    ( k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(trivial_inequality_removal,[],[f214])).

fof(f214,plain,
    ( sK1 != sK1
    | k1_xboole_0 = sK1
    | ~ v2_funct_1(sK2)
    | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ v1_funct_1(sK2)
    | ~ spl4_6 ),
    inference(superposition,[],[f212,f112])).

fof(f202,plain,
    ( spl4_18
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(avatar_split_clause,[],[f197,f146,f140,f130,f125,f115,f199])).

fof(f197,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_12
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f196,f142])).

fof(f196,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_10
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f195,f132])).

fof(f195,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_9
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f194,f127])).

fof(f194,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_7
    | ~ spl4_13 ),
    inference(subsumption_resolution,[],[f191,f117])).

fof(f191,plain,
    ( r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ v1_funct_1(sK2)
    | ~ spl4_13 ),
    inference(superposition,[],[f148,f75])).

fof(f165,plain,
    ( spl4_15
    | ~ spl4_10 ),
    inference(avatar_split_clause,[],[f160,f130,f162])).

fof(f160,plain,
    ( v1_relat_1(sK2)
    | ~ spl4_10 ),
    inference(subsumption_resolution,[],[f152,f79])).

fof(f79,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f152,plain,
    ( v1_relat_1(sK2)
    | ~ v1_relat_1(k2_zfmisc_1(sK0,sK1))
    | ~ spl4_10 ),
    inference(resolution,[],[f78,f132])).

fof(f78,plain,(
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
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f159,plain,
    ( spl4_14
    | ~ spl4_7 ),
    inference(avatar_split_clause,[],[f154,f115,f156])).

fof(f154,plain,
    ( v1_relat_1(sK3)
    | ~ spl4_7 ),
    inference(subsumption_resolution,[],[f151,f79])).

fof(f151,plain,
    ( v1_relat_1(sK3)
    | ~ v1_relat_1(k2_zfmisc_1(sK1,sK0))
    | ~ spl4_7 ),
    inference(resolution,[],[f78,f117])).

fof(f149,plain,
    ( spl4_13
    | ~ spl4_5 ),
    inference(avatar_split_clause,[],[f144,f105,f146])).

fof(f105,plain,
    ( spl4_5
  <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).

fof(f144,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))
    | ~ spl4_5 ),
    inference(backward_demodulation,[],[f107,f72])).

fof(f107,plain,
    ( r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))
    | ~ spl4_5 ),
    inference(avatar_component_clause,[],[f105])).

fof(f143,plain,(
    spl4_12 ),
    inference(avatar_split_clause,[],[f44,f140])).

fof(f44,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f41,f40])).

fof(f40,plain,
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

fof(f41,plain,
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

fof(f20,plain,(
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
    inference(flattening,[],[f19])).

fof(f19,plain,(
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
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
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
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
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

fof(f138,plain,(
    spl4_11 ),
    inference(avatar_split_clause,[],[f45,f135])).

fof(f45,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f42])).

fof(f133,plain,(
    spl4_10 ),
    inference(avatar_split_clause,[],[f46,f130])).

fof(f46,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f42])).

fof(f128,plain,(
    spl4_9 ),
    inference(avatar_split_clause,[],[f47,f125])).

fof(f47,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f42])).

% (17541)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
fof(f123,plain,(
    spl4_8 ),
    inference(avatar_split_clause,[],[f48,f120])).

fof(f48,plain,(
    v1_funct_2(sK3,sK1,sK0) ),
    inference(cnf_transformation,[],[f42])).

fof(f118,plain,(
    spl4_7 ),
    inference(avatar_split_clause,[],[f49,f115])).

fof(f49,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f42])).

fof(f113,plain,(
    spl4_6 ),
    inference(avatar_split_clause,[],[f50,f110])).

fof(f50,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f108,plain,(
    spl4_5 ),
    inference(avatar_split_clause,[],[f51,f105])).

fof(f51,plain,(
    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) ),
    inference(cnf_transformation,[],[f42])).

fof(f103,plain,(
    spl4_4 ),
    inference(avatar_split_clause,[],[f52,f100])).

fof(f52,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f42])).

fof(f98,plain,(
    ~ spl4_3 ),
    inference(avatar_split_clause,[],[f53,f95])).

fof(f53,plain,(
    k1_xboole_0 != sK0 ),
    inference(cnf_transformation,[],[f42])).

fof(f93,plain,(
    ~ spl4_2 ),
    inference(avatar_split_clause,[],[f54,f90])).

fof(f54,plain,(
    k1_xboole_0 != sK1 ),
    inference(cnf_transformation,[],[f42])).

fof(f88,plain,(
    ~ spl4_1 ),
    inference(avatar_split_clause,[],[f55,f85])).

fof(f55,plain,(
    k2_funct_1(sK2) != sK3 ),
    inference(cnf_transformation,[],[f42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 10:27:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.49  % (17528)lrs+1011_1_afp=40000:afq=1.4:bd=off:cond=fast:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sd=2:ss=axioms:sos=all:sp=occurrence_6 on theBenchmark
% 0.22/0.50  % (17516)dis+10_16_awrs=decay:awrsf=256:afr=on:afp=40000:afq=2.0:amm=off:bsr=on:cond=on:er=known:gsp=input_only:irw=on:lma=on:nm=6:newcnf=on:nwc=3:sas=z3:sd=4:ss=axioms:s2a=on:sp=frequency:updr=off_8 on theBenchmark
% 0.22/0.51  % (17520)dis+1002_8:1_av=off:br=off:cond=on:irw=on:lma=on:nm=32:nwc=1:sp=occurrence:urr=on_89 on theBenchmark
% 0.22/0.52  % (17523)lrs+1_8:1_av=off:cond=fast:fde=unused:lcm=predicate:nm=16:nwc=10:stl=60:sp=occurrence:urr=ec_only_3 on theBenchmark
% 0.22/0.52  % (17537)dis+1010_3:2_acc=on:afr=on:afp=1000:afq=1.2:amm=sco:bs=on:ccuc=first:fde=none:nm=0:nwc=4:sd=3:ss=axioms:st=5.0:urr=ec_only_75 on theBenchmark
% 0.22/0.52  % (17518)dis+1_5:1_aac=none:afr=on:afp=100000:afq=1.4:amm=sco:anc=none:br=off:gsp=input_only:gs=on:gsem=on:lcm=reverse:nm=6:nwc=1:nicw=on:sas=z3:sos=on:urr=on_1 on theBenchmark
% 0.22/0.52  % (17527)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_23 on theBenchmark
% 0.22/0.53  % (17517)dis+11_3_av=off:fsr=off:lcm=predicate:lma=on:nm=4:nwc=1:sd=3:ss=axioms:st=1.2:sos=on:updr=off_4 on theBenchmark
% 0.22/0.53  % (17536)ott+4_4:1_acc=model:add=large:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=preordered:bs=unit_only:ccuc=first:cond=on:gs=on:nm=32:nwc=1.5:sac=on:urr=on:updr=off_13 on theBenchmark
% 0.22/0.53  % (17521)dis-1_2:3_av=off:cond=on:fsr=off:irw=on:lma=on:nwc=3:sd=3:ss=axioms:st=3.0:sp=occurrence:updr=off_9 on theBenchmark
% 0.22/0.54  % (17533)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_36 on theBenchmark
% 0.22/0.54  % (17538)lrs+1011_2:3_av=off:gs=on:gsem=off:nwc=1.5:stl=30:sos=theory:sp=occurrence:urr=ec_only:updr=off_223 on theBenchmark
% 0.22/0.54  % (17524)lrs+11_3_afr=on:afp=10000:afq=1.0:cond=fast:fsr=off:fde=none:gs=on:gsem=off:lcm=reverse:nm=2:newcnf=on:nwc=1:sas=z3:stl=30:sd=10:ss=axioms:st=2.0:sos=all:sp=reverse_arity:urr=on:uhcvi=on_23 on theBenchmark
% 0.22/0.54  % (17540)dis-11_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:gs=on:irw=on:lcm=reverse:nm=6:nwc=1:sd=4:ss=axioms:st=3.0:sos=on:sac=on_1 on theBenchmark
% 0.22/0.54  % (17530)lrs+10_1_av=off:fde=unused:irw=on:lcm=predicate:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=5.0:sos=on:sp=reverse_arity_2 on theBenchmark
% 0.22/0.54  % (17519)dis+11_2:1_add=large:afp=1000:afq=1.2:amm=sco:anc=none:cond=on:gs=on:gsem=off:nm=16:newcnf=on:nwc=1:sas=z3:sd=1:ss=axioms:st=1.2:sos=on:sp=reverse_arity:updr=off_5 on theBenchmark
% 0.22/0.54  % (17531)dis+1011_3_afp=4000:afq=1.1:amm=sco:anc=none:gs=on:gsaa=from_current:gsem=off:irw=on:nm=16:nwc=1:sas=z3:ss=axioms:sos=all:sac=on:sp=reverse_arity:updr=off_17 on theBenchmark
% 0.22/0.55  % (17525)lrs+1002_1_av=off:fde=unused:lwlo=on:nm=16:nwc=4:stl=30:sp=occurrence_66 on theBenchmark
% 0.22/0.55  % (17522)dis+10_3_add=off:afp=40000:afq=1.0:amm=sco:anc=none:er=filter:gs=on:gsem=off:irw=on:lma=on:nm=4:nwc=1.3:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.22/0.55  % (17535)lrs+1011_3:2_av=off:er=known:lma=on:nm=2:newcnf=on:nwc=2:stl=30:sd=2:ss=axioms:st=3.0:urr=on:updr=off_24 on theBenchmark
% 0.22/0.55  % (17532)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_9 on theBenchmark
% 0.22/0.55  % (17526)dis+1002_7_acc=on:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:ccuc=first:fsr=off:gsp=input_only:gs=on:gsem=on:nm=6:nwc=1.1:nicw=on:sos=on:sac=on:sp=occurrence:urr=ec_only_217 on theBenchmark
% 0.22/0.55  % (17532)Refutation not found, incomplete strategy% (17532)------------------------------
% 0.22/0.55  % (17532)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.22/0.55  % (17532)Termination reason: Refutation not found, incomplete strategy
% 0.22/0.55  
% 0.22/0.55  % (17532)Memory used [KB]: 10746
% 0.22/0.55  % (17532)Time elapsed: 0.137 s
% 0.22/0.55  % (17532)------------------------------
% 0.22/0.55  % (17532)------------------------------
% 0.22/0.56  % (17543)lrs-4_5:1_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:bs=unit_only:bsr=on:irw=on:lcm=reverse:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:updr=off_6 on theBenchmark
% 0.22/0.56  % (17544)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_73 on theBenchmark
% 0.22/0.56  % (17542)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_11 on theBenchmark
% 0.22/0.56  % (17537)Refutation found. Thanks to Tanya!
% 0.22/0.56  % SZS status Theorem for theBenchmark
% 0.22/0.56  % SZS output start Proof for theBenchmark
% 0.22/0.56  fof(f787,plain,(
% 0.22/0.56    $false),
% 0.22/0.56    inference(avatar_sat_refutation,[],[f88,f93,f98,f103,f108,f113,f118,f123,f128,f133,f138,f143,f149,f159,f165,f202,f225,f241,f253,f277,f292,f318,f355,f405,f428,f437,f459,f494,f519,f552,f633,f786])).
% 0.22/0.56  fof(f786,plain,(
% 0.22/0.56    spl4_46 | ~spl4_57),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f785])).
% 0.22/0.56  fof(f785,plain,(
% 0.22/0.56    $false | (spl4_46 | ~spl4_57)),
% 0.22/0.56    inference(subsumption_resolution,[],[f784,f493])).
% 0.22/0.56  fof(f493,plain,(
% 0.22/0.56    sK1 != k1_relat_1(sK3) | spl4_46),
% 0.22/0.56    inference(avatar_component_clause,[],[f491])).
% 0.22/0.56  fof(f491,plain,(
% 0.22/0.56    spl4_46 <=> sK1 = k1_relat_1(sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_46])])).
% 0.22/0.56  fof(f784,plain,(
% 0.22/0.56    sK1 = k1_relat_1(sK3) | ~spl4_57),
% 0.22/0.56    inference(forward_demodulation,[],[f775,f77])).
% 0.22/0.56  fof(f77,plain,(
% 0.22/0.56    ( ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f3])).
% 0.22/0.56  fof(f3,axiom,(
% 0.22/0.56    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_relat_1)).
% 0.22/0.56  fof(f775,plain,(
% 0.22/0.56    k1_relat_1(sK3) = k2_relat_1(k6_relat_1(sK1)) | ~spl4_57),
% 0.22/0.56    inference(superposition,[],[f77,f628])).
% 0.22/0.56  fof(f628,plain,(
% 0.22/0.56    k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3)) | ~spl4_57),
% 0.22/0.56    inference(avatar_component_clause,[],[f626])).
% 0.22/0.56  fof(f626,plain,(
% 0.22/0.56    spl4_57 <=> k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_57])])).
% 0.22/0.56  fof(f633,plain,(
% 0.22/0.56    spl4_57 | ~spl4_9 | ~spl4_14 | ~spl4_27 | ~spl4_28),
% 0.22/0.56    inference(avatar_split_clause,[],[f632,f315,f306,f156,f125,f626])).
% 0.22/0.56  fof(f125,plain,(
% 0.22/0.56    spl4_9 <=> v1_funct_1(sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_9])])).
% 0.22/0.56  fof(f156,plain,(
% 0.22/0.56    spl4_14 <=> v1_relat_1(sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_14])])).
% 0.22/0.56  fof(f306,plain,(
% 0.22/0.56    spl4_27 <=> v2_funct_1(sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_27])])).
% 0.22/0.56  fof(f315,plain,(
% 0.22/0.56    spl4_28 <=> k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_28])])).
% 0.22/0.56  fof(f632,plain,(
% 0.22/0.56    k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3)) | (~spl4_9 | ~spl4_14 | ~spl4_27 | ~spl4_28)),
% 0.22/0.56    inference(subsumption_resolution,[],[f631,f158])).
% 0.22/0.56  fof(f158,plain,(
% 0.22/0.56    v1_relat_1(sK3) | ~spl4_14),
% 0.22/0.56    inference(avatar_component_clause,[],[f156])).
% 0.22/0.56  fof(f631,plain,(
% 0.22/0.56    k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3)) | ~v1_relat_1(sK3) | (~spl4_9 | ~spl4_27 | ~spl4_28)),
% 0.22/0.56    inference(subsumption_resolution,[],[f630,f127])).
% 0.22/0.56  fof(f127,plain,(
% 0.22/0.56    v1_funct_1(sK3) | ~spl4_9),
% 0.22/0.56    inference(avatar_component_clause,[],[f125])).
% 0.22/0.56  fof(f630,plain,(
% 0.22/0.56    k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3)) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | (~spl4_27 | ~spl4_28)),
% 0.22/0.56    inference(subsumption_resolution,[],[f617,f307])).
% 0.22/0.56  fof(f307,plain,(
% 0.22/0.56    v2_funct_1(sK3) | ~spl4_27),
% 0.22/0.56    inference(avatar_component_clause,[],[f306])).
% 0.22/0.56  fof(f617,plain,(
% 0.22/0.56    k6_relat_1(sK1) = k6_relat_1(k1_relat_1(sK3)) | ~v2_funct_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~spl4_28),
% 0.22/0.56    inference(superposition,[],[f59,f317])).
% 0.22/0.56  fof(f317,plain,(
% 0.22/0.56    k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~spl4_28),
% 0.22/0.56    inference(avatar_component_clause,[],[f315])).
% 0.22/0.56  fof(f59,plain,(
% 0.22/0.56    ( ! [X0] : (k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f26,plain,(
% 0.22/0.56    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(flattening,[],[f25])).
% 0.22/0.56  fof(f25,plain,(
% 0.22/0.56    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f6])).
% 0.22/0.56  fof(f6,axiom,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k6_relat_1(k1_relat_1(X0)) = k5_relat_1(X0,k2_funct_1(X0)))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.22/0.56  fof(f552,plain,(
% 0.22/0.56    spl4_27 | spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_41),
% 0.22/0.56    inference(avatar_split_clause,[],[f551,f425,f140,f135,f130,f125,f120,f115,f110,f95,f306])).
% 0.22/0.56  fof(f95,plain,(
% 0.22/0.56    spl4_3 <=> k1_xboole_0 = sK0),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_3])])).
% 0.22/0.56  fof(f110,plain,(
% 0.22/0.56    spl4_6 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_6])])).
% 0.22/0.56  fof(f115,plain,(
% 0.22/0.56    spl4_7 <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_7])])).
% 0.22/0.56  fof(f120,plain,(
% 0.22/0.56    spl4_8 <=> v1_funct_2(sK3,sK1,sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_8])])).
% 0.22/0.56  fof(f130,plain,(
% 0.22/0.56    spl4_10 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_10])])).
% 0.22/0.56  fof(f135,plain,(
% 0.22/0.56    spl4_11 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_11])])).
% 0.22/0.56  fof(f140,plain,(
% 0.22/0.56    spl4_12 <=> v1_funct_1(sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_12])])).
% 0.22/0.56  fof(f425,plain,(
% 0.22/0.56    spl4_41 <=> k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_41])])).
% 0.22/0.56  fof(f551,plain,(
% 0.22/0.56    v2_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_41)),
% 0.22/0.56    inference(subsumption_resolution,[],[f550,f127])).
% 0.22/0.56  fof(f550,plain,(
% 0.22/0.56    v2_funct_1(sK3) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_41)),
% 0.22/0.56    inference(subsumption_resolution,[],[f549,f122])).
% 0.22/0.56  fof(f122,plain,(
% 0.22/0.56    v1_funct_2(sK3,sK1,sK0) | ~spl4_8),
% 0.22/0.56    inference(avatar_component_clause,[],[f120])).
% 0.22/0.56  fof(f549,plain,(
% 0.22/0.56    v2_funct_1(sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_41)),
% 0.22/0.56    inference(subsumption_resolution,[],[f548,f117])).
% 0.22/0.56  fof(f117,plain,(
% 0.22/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~spl4_7),
% 0.22/0.56    inference(avatar_component_clause,[],[f115])).
% 0.22/0.56  fof(f548,plain,(
% 0.22/0.56    v2_funct_1(sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_41)),
% 0.22/0.56    inference(subsumption_resolution,[],[f537,f97])).
% 0.22/0.56  fof(f97,plain,(
% 0.22/0.56    k1_xboole_0 != sK0 | spl4_3),
% 0.22/0.56    inference(avatar_component_clause,[],[f95])).
% 0.22/0.56  fof(f537,plain,(
% 0.22/0.56    v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_41)),
% 0.22/0.56    inference(subsumption_resolution,[],[f529,f67])).
% 0.22/0.56  fof(f67,plain,(
% 0.22/0.56    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f4])).
% 0.22/0.56  fof(f4,axiom,(
% 0.22/0.56    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_funct_1)).
% 0.22/0.56  fof(f529,plain,(
% 0.22/0.56    ~v2_funct_1(k6_relat_1(sK0)) | v2_funct_1(sK3) | k1_xboole_0 = sK0 | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_41)),
% 0.22/0.56    inference(superposition,[],[f336,f427])).
% 0.22/0.56  fof(f427,plain,(
% 0.22/0.56    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~spl4_41),
% 0.22/0.56    inference(avatar_component_clause,[],[f425])).
% 0.22/0.56  fof(f336,plain,(
% 0.22/0.56    ( ! [X0,X1] : (~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | v2_funct_1(X1) | k1_xboole_0 = X0 | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 0.22/0.56    inference(subsumption_resolution,[],[f335,f142])).
% 0.22/0.56  fof(f142,plain,(
% 0.22/0.56    v1_funct_1(sK2) | ~spl4_12),
% 0.22/0.56    inference(avatar_component_clause,[],[f140])).
% 0.22/0.56  fof(f335,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10 | ~spl4_11)),
% 0.22/0.56    inference(subsumption_resolution,[],[f334,f137])).
% 0.22/0.56  fof(f137,plain,(
% 0.22/0.56    v1_funct_2(sK2,sK0,sK1) | ~spl4_11),
% 0.22/0.56    inference(avatar_component_clause,[],[f135])).
% 0.22/0.56  fof(f334,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | (~spl4_6 | ~spl4_10)),
% 0.22/0.56    inference(subsumption_resolution,[],[f333,f132])).
% 0.22/0.56  fof(f132,plain,(
% 0.22/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl4_10),
% 0.22/0.56    inference(avatar_component_clause,[],[f130])).
% 0.22/0.56  fof(f333,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_6),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f330])).
% 0.22/0.56  fof(f330,plain,(
% 0.22/0.56    ( ! [X0,X1] : (sK1 != sK1 | k1_xboole_0 = X0 | v2_funct_1(X1) | ~v2_funct_1(k1_partfun1(sK0,sK1,sK1,X0,sK2,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK1,X0))) | ~v1_funct_2(X1,sK1,X0) | ~v1_funct_1(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2)) ) | ~spl4_6),
% 0.22/0.56    inference(superposition,[],[f63,f112])).
% 0.22/0.56  fof(f112,plain,(
% 0.22/0.56    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl4_6),
% 0.22/0.56    inference(avatar_component_clause,[],[f110])).
% 0.22/0.56  fof(f63,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X3,X1] : (k2_relset_1(X0,X1,X3) != X1 | k1_xboole_0 = X2 | v2_funct_1(X4) | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f28])).
% 0.22/0.56  fof(f28,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (! [X4] : ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2) | k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3))),
% 0.22/0.56    inference(flattening,[],[f27])).
% 0.22/0.56  fof(f27,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (! [X4] : ((((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)) | (k2_relset_1(X0,X1,X3) != X1 | ~v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4)))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X4,X1,X2) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)))),
% 0.22/0.56    inference(ennf_transformation,[],[f14])).
% 0.22/0.56  fof(f14,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) & v1_funct_2(X4,X1,X2) & v1_funct_1(X4)) => ((k2_relset_1(X0,X1,X3) = X1 & v2_funct_1(k1_partfun1(X0,X1,X1,X2,X3,X4))) => ((v2_funct_1(X4) & v2_funct_1(X3)) | (k1_xboole_0 != X1 & k1_xboole_0 = X2)))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t30_funct_2)).
% 0.22/0.56  fof(f519,plain,(
% 0.22/0.56    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_40),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f518])).
% 0.22/0.56  fof(f518,plain,(
% 0.22/0.56    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_40)),
% 0.22/0.56    inference(subsumption_resolution,[],[f517,f142])).
% 0.22/0.56  fof(f517,plain,(
% 0.22/0.56    ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | spl4_40)),
% 0.22/0.56    inference(subsumption_resolution,[],[f516,f132])).
% 0.22/0.56  fof(f516,plain,(
% 0.22/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | spl4_40)),
% 0.22/0.56    inference(subsumption_resolution,[],[f515,f127])).
% 0.22/0.56  fof(f515,plain,(
% 0.22/0.56    ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | spl4_40)),
% 0.22/0.56    inference(subsumption_resolution,[],[f512,f117])).
% 0.22/0.56  fof(f512,plain,(
% 0.22/0.56    ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | spl4_40),
% 0.22/0.56    inference(resolution,[],[f423,f74])).
% 0.22/0.56  fof(f74,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f36])).
% 0.22/0.56  fof(f36,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.22/0.56    inference(flattening,[],[f35])).
% 0.22/0.56  fof(f35,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.22/0.56    inference(ennf_transformation,[],[f9])).
% 0.22/0.56  fof(f9,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => (m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5))))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k1_partfun1)).
% 0.22/0.56  fof(f423,plain,(
% 0.22/0.56    ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_40),
% 0.22/0.56    inference(avatar_component_clause,[],[f421])).
% 0.22/0.56  fof(f421,plain,(
% 0.22/0.56    spl4_40 <=> m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_40])])).
% 0.22/0.56  fof(f494,plain,(
% 0.22/0.56    ~spl4_46 | spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_24 | ~spl4_37 | ~spl4_43),
% 0.22/0.56    inference(avatar_split_clause,[],[f489,f434,f400,f272,f162,f156,f140,f125,f85,f491])).
% 0.22/0.56  fof(f85,plain,(
% 0.22/0.56    spl4_1 <=> k2_funct_1(sK2) = sK3),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_1])])).
% 0.22/0.56  fof(f162,plain,(
% 0.22/0.56    spl4_15 <=> v1_relat_1(sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_15])])).
% 0.22/0.56  fof(f272,plain,(
% 0.22/0.56    spl4_24 <=> sK0 = k1_relat_1(sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_24])])).
% 0.22/0.56  fof(f400,plain,(
% 0.22/0.56    spl4_37 <=> sK1 = k2_relat_1(sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_37])])).
% 0.22/0.56  fof(f434,plain,(
% 0.22/0.56    spl4_43 <=> k6_relat_1(sK0) = k5_relat_1(sK2,sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_43])])).
% 0.22/0.56  fof(f489,plain,(
% 0.22/0.56    sK1 != k1_relat_1(sK3) | (spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_24 | ~spl4_37 | ~spl4_43)),
% 0.22/0.56    inference(forward_demodulation,[],[f488,f402])).
% 0.22/0.56  fof(f402,plain,(
% 0.22/0.56    sK1 = k2_relat_1(sK2) | ~spl4_37),
% 0.22/0.56    inference(avatar_component_clause,[],[f400])).
% 0.22/0.56  fof(f488,plain,(
% 0.22/0.56    k2_relat_1(sK2) != k1_relat_1(sK3) | (spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_24 | ~spl4_43)),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f487])).
% 0.22/0.56  fof(f487,plain,(
% 0.22/0.56    k6_relat_1(sK0) != k6_relat_1(sK0) | k2_relat_1(sK2) != k1_relat_1(sK3) | (spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_24 | ~spl4_43)),
% 0.22/0.56    inference(forward_demodulation,[],[f486,f274])).
% 0.22/0.56  fof(f274,plain,(
% 0.22/0.56    sK0 = k1_relat_1(sK2) | ~spl4_24),
% 0.22/0.56    inference(avatar_component_clause,[],[f272])).
% 0.22/0.56  fof(f486,plain,(
% 0.22/0.56    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(sK3) | (spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_15 | ~spl4_43)),
% 0.22/0.56    inference(subsumption_resolution,[],[f485,f164])).
% 0.22/0.56  fof(f164,plain,(
% 0.22/0.56    v1_relat_1(sK2) | ~spl4_15),
% 0.22/0.56    inference(avatar_component_clause,[],[f162])).
% 0.22/0.56  fof(f485,plain,(
% 0.22/0.56    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_9 | ~spl4_12 | ~spl4_14 | ~spl4_43)),
% 0.22/0.56    inference(subsumption_resolution,[],[f484,f142])).
% 0.22/0.56  fof(f484,plain,(
% 0.22/0.56    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_9 | ~spl4_14 | ~spl4_43)),
% 0.22/0.56    inference(subsumption_resolution,[],[f483,f158])).
% 0.22/0.56  fof(f483,plain,(
% 0.22/0.56    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_9 | ~spl4_43)),
% 0.22/0.56    inference(subsumption_resolution,[],[f482,f127])).
% 0.22/0.56  fof(f482,plain,(
% 0.22/0.56    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl4_1 | ~spl4_43)),
% 0.22/0.56    inference(subsumption_resolution,[],[f478,f87])).
% 0.22/0.56  fof(f87,plain,(
% 0.22/0.56    k2_funct_1(sK2) != sK3 | spl4_1),
% 0.22/0.56    inference(avatar_component_clause,[],[f85])).
% 0.22/0.56  fof(f478,plain,(
% 0.22/0.56    k6_relat_1(sK0) != k6_relat_1(k1_relat_1(sK2)) | k2_funct_1(sK2) = sK3 | k2_relat_1(sK2) != k1_relat_1(sK3) | ~v1_funct_1(sK3) | ~v1_relat_1(sK3) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_43),
% 0.22/0.56    inference(superposition,[],[f186,f436])).
% 0.22/0.56  fof(f436,plain,(
% 0.22/0.56    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~spl4_43),
% 0.22/0.56    inference(avatar_component_clause,[],[f434])).
% 0.22/0.56  fof(f186,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_funct_1(X0) = X1 | k2_relat_1(X0) != k1_relat_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(subsumption_resolution,[],[f58,f65])).
% 0.22/0.56  fof(f65,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f30])).
% 0.22/0.56  fof(f30,plain,(
% 0.22/0.56    ! [X0] : (v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(flattening,[],[f29])).
% 0.22/0.56  fof(f29,plain,(
% 0.22/0.56    ! [X0] : ((v2_funct_1(X0) | ! [X1] : (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f5])).
% 0.22/0.56  fof(f5,axiom,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (? [X1] : (k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & v1_funct_1(X1) & v1_relat_1(X1)) => v2_funct_1(X0)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_funct_1)).
% 0.22/0.56  fof(f58,plain,(
% 0.22/0.56    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f24])).
% 0.22/0.56  fof(f24,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.22/0.56    inference(flattening,[],[f23])).
% 0.22/0.56  fof(f23,plain,(
% 0.22/0.56    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X0,X1) != k6_relat_1(k1_relat_1(X0)) | k2_relat_1(X0) != k1_relat_1(X1) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.22/0.56    inference(ennf_transformation,[],[f7])).
% 0.22/0.56  fof(f7,axiom,(
% 0.22/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X0,X1) = k6_relat_1(k1_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(X1) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_funct_1)).
% 0.22/0.56  fof(f459,plain,(
% 0.22/0.56    ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_42),
% 0.22/0.56    inference(avatar_contradiction_clause,[],[f445])).
% 0.22/0.56  fof(f445,plain,(
% 0.22/0.56    $false | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | spl4_42)),
% 0.22/0.56    inference(unit_resulting_resolution,[],[f142,f127,f132,f117,f432,f208])).
% 0.22/0.56  fof(f208,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.22/0.56    inference(duplicate_literal_removal,[],[f207])).
% 0.22/0.56  fof(f207,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k5_relat_1(X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.22/0.56    inference(superposition,[],[f74,f75])).
% 0.22/0.56  % (17534)ott-3_3_av=off:cond=fast:fde=none:lcm=reverse:nm=6:nwc=1:sd=5:ss=axioms:st=2.0:sos=on:sp=reverse_arity:updr=off:uhcvi=on_88 on theBenchmark
% 0.22/0.56  fof(f75,plain,(
% 0.22/0.56    ( ! [X4,X2,X0,X5,X3,X1] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f38])).
% 0.22/0.56  fof(f38,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.22/0.56    inference(flattening,[],[f37])).
% 0.22/0.56  fof(f37,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.22/0.56    inference(ennf_transformation,[],[f11])).
% 0.22/0.56  fof(f11,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.22/0.56  fof(f432,plain,(
% 0.22/0.56    ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | spl4_42),
% 0.22/0.56    inference(avatar_component_clause,[],[f430])).
% 0.22/0.56  fof(f430,plain,(
% 0.22/0.56    spl4_42 <=> m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0)))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_42])])).
% 0.22/0.56  fof(f437,plain,(
% 0.22/0.56    ~spl4_42 | spl4_43 | ~spl4_18),
% 0.22/0.56    inference(avatar_split_clause,[],[f417,f199,f434,f430])).
% 0.22/0.56  fof(f199,plain,(
% 0.22/0.56    spl4_18 <=> r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_18])])).
% 0.22/0.56  fof(f417,plain,(
% 0.22/0.56    k6_relat_1(sK0) = k5_relat_1(sK2,sK3) | ~m1_subset_1(k5_relat_1(sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_18),
% 0.22/0.56    inference(resolution,[],[f185,f201])).
% 0.22/0.56  fof(f201,plain,(
% 0.22/0.56    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~spl4_18),
% 0.22/0.56    inference(avatar_component_clause,[],[f199])).
% 0.22/0.56  fof(f185,plain,(
% 0.22/0.56    ( ! [X2,X3] : (~r2_relset_1(X2,X2,X3,k6_relat_1(X2)) | k6_relat_1(X2) = X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X2,X2)))) )),
% 0.22/0.56    inference(resolution,[],[f68,f150])).
% 0.22/0.56  fof(f150,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k6_relat_1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.56    inference(forward_demodulation,[],[f71,f72])).
% 0.22/0.56  fof(f72,plain,(
% 0.22/0.56    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f12])).
% 0.22/0.56  fof(f12,axiom,(
% 0.22/0.56    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.22/0.56  fof(f71,plain,(
% 0.22/0.56    ( ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f18])).
% 0.22/0.56  fof(f18,plain,(
% 0.22/0.56    ! [X0] : m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0)))),
% 0.22/0.56    inference(pure_predicate_removal,[],[f10])).
% 0.22/0.56  fof(f10,axiom,(
% 0.22/0.56    ! [X0] : (m1_subset_1(k6_partfun1(X0),k1_zfmisc_1(k2_zfmisc_1(X0,X0))) & v1_partfun1(k6_partfun1(X0),X0))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k6_partfun1)).
% 0.22/0.56  fof(f68,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~r2_relset_1(X0,X1,X2,X3) | X2 = X3 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.22/0.56    inference(cnf_transformation,[],[f43])).
% 0.22/0.56  fof(f43,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : (((r2_relset_1(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_relset_1(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(nnf_transformation,[],[f32])).
% 0.22/0.56  fof(f32,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.22/0.56    inference(flattening,[],[f31])).
% 0.22/0.56  fof(f31,plain,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((r2_relset_1(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))))),
% 0.22/0.56    inference(ennf_transformation,[],[f8])).
% 0.22/0.56  fof(f8,axiom,(
% 0.22/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) => (r2_relset_1(X0,X1,X2,X3) <=> X2 = X3))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_r2_relset_1)).
% 0.22/0.56  fof(f428,plain,(
% 0.22/0.56    ~spl4_40 | spl4_41 | ~spl4_13),
% 0.22/0.56    inference(avatar_split_clause,[],[f416,f146,f425,f421])).
% 0.22/0.56  fof(f146,plain,(
% 0.22/0.56    spl4_13 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_13])])).
% 0.22/0.56  fof(f416,plain,(
% 0.22/0.56    k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3) = k6_relat_1(sK0) | ~m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k1_zfmisc_1(k2_zfmisc_1(sK0,sK0))) | ~spl4_13),
% 0.22/0.56    inference(resolution,[],[f185,f148])).
% 0.22/0.56  fof(f148,plain,(
% 0.22/0.56    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_13),
% 0.22/0.56    inference(avatar_component_clause,[],[f146])).
% 0.22/0.56  fof(f405,plain,(
% 0.22/0.56    spl4_37 | ~spl4_30),
% 0.22/0.56    inference(avatar_split_clause,[],[f404,f348,f400])).
% 0.22/0.56  fof(f348,plain,(
% 0.22/0.56    spl4_30 <=> k6_relat_1(k2_relat_1(sK2)) = k6_relat_1(sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_30])])).
% 0.22/0.56  fof(f404,plain,(
% 0.22/0.56    sK1 = k2_relat_1(sK2) | ~spl4_30),
% 0.22/0.56    inference(forward_demodulation,[],[f394,f77])).
% 0.22/0.56  fof(f394,plain,(
% 0.22/0.56    k2_relat_1(sK2) = k2_relat_1(k6_relat_1(sK1)) | ~spl4_30),
% 0.22/0.56    inference(superposition,[],[f77,f350])).
% 0.22/0.56  fof(f350,plain,(
% 0.22/0.56    k6_relat_1(k2_relat_1(sK2)) = k6_relat_1(sK1) | ~spl4_30),
% 0.22/0.56    inference(avatar_component_clause,[],[f348])).
% 0.22/0.56  fof(f355,plain,(
% 0.22/0.56    spl4_30 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_21),
% 0.22/0.56    inference(avatar_split_clause,[],[f354,f250,f162,f140,f100,f348])).
% 0.22/0.56  fof(f100,plain,(
% 0.22/0.56    spl4_4 <=> v2_funct_1(sK2)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_4])])).
% 0.22/0.56  fof(f250,plain,(
% 0.22/0.56    spl4_21 <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_21])])).
% 0.22/0.56  fof(f354,plain,(
% 0.22/0.56    k6_relat_1(k2_relat_1(sK2)) = k6_relat_1(sK1) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_21)),
% 0.22/0.56    inference(subsumption_resolution,[],[f353,f164])).
% 0.22/0.56  fof(f353,plain,(
% 0.22/0.56    k6_relat_1(k2_relat_1(sK2)) = k6_relat_1(sK1) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_21)),
% 0.22/0.56    inference(subsumption_resolution,[],[f352,f142])).
% 0.22/0.56  fof(f352,plain,(
% 0.22/0.56    k6_relat_1(k2_relat_1(sK2)) = k6_relat_1(sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_21)),
% 0.22/0.56    inference(subsumption_resolution,[],[f341,f102])).
% 0.22/0.56  fof(f102,plain,(
% 0.22/0.56    v2_funct_1(sK2) | ~spl4_4),
% 0.22/0.56    inference(avatar_component_clause,[],[f100])).
% 0.22/0.56  fof(f341,plain,(
% 0.22/0.56    k6_relat_1(k2_relat_1(sK2)) = k6_relat_1(sK1) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_21),
% 0.22/0.56    inference(superposition,[],[f60,f252])).
% 0.22/0.56  fof(f252,plain,(
% 0.22/0.56    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~spl4_21),
% 0.22/0.56    inference(avatar_component_clause,[],[f250])).
% 0.22/0.56  fof(f60,plain,(
% 0.22/0.56    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f26])).
% 0.22/0.56  fof(f318,plain,(
% 0.22/0.56    spl4_28 | ~spl4_27 | spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_25),
% 0.22/0.56    inference(avatar_split_clause,[],[f313,f289,f125,f120,f115,f95,f306,f315])).
% 0.22/0.56  fof(f289,plain,(
% 0.22/0.56    spl4_25 <=> sK0 = k2_relset_1(sK1,sK0,sK3)),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_25])])).
% 0.22/0.56  fof(f313,plain,(
% 0.22/0.56    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_25)),
% 0.22/0.56    inference(subsumption_resolution,[],[f312,f127])).
% 0.22/0.56  fof(f312,plain,(
% 0.22/0.56    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_8 | ~spl4_25)),
% 0.22/0.56    inference(subsumption_resolution,[],[f311,f122])).
% 0.22/0.56  fof(f311,plain,(
% 0.22/0.56    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_7 | ~spl4_25)),
% 0.22/0.56    inference(subsumption_resolution,[],[f310,f117])).
% 0.22/0.56  fof(f310,plain,(
% 0.22/0.56    ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (spl4_3 | ~spl4_25)),
% 0.22/0.56    inference(subsumption_resolution,[],[f295,f97])).
% 0.22/0.56  fof(f295,plain,(
% 0.22/0.56    k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_25),
% 0.22/0.56    inference(trivial_inequality_removal,[],[f294])).
% 0.22/0.56  fof(f294,plain,(
% 0.22/0.56    sK0 != sK0 | k1_xboole_0 = sK0 | ~v2_funct_1(sK3) | k6_relat_1(sK1) = k5_relat_1(sK3,k2_funct_1(sK3)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_25),
% 0.22/0.56    inference(superposition,[],[f212,f291])).
% 0.22/0.56  fof(f291,plain,(
% 0.22/0.56    sK0 = k2_relset_1(sK1,sK0,sK3) | ~spl4_25),
% 0.22/0.56    inference(avatar_component_clause,[],[f289])).
% 0.22/0.56  fof(f212,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k6_relat_1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f56,f72])).
% 0.22/0.56  fof(f56,plain,(
% 0.22/0.56    ( ! [X2,X0,X1] : (k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f22])).
% 0.22/0.56  fof(f22,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.56    inference(flattening,[],[f21])).
% 0.22/0.56  fof(f21,plain,(
% 0.22/0.56    ! [X0,X1,X2] : ((((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.56    inference(ennf_transformation,[],[f15])).
% 0.22/0.56  fof(f15,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_funct_2)).
% 0.22/0.56  fof(f292,plain,(
% 0.22/0.56    spl4_25 | ~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13),
% 0.22/0.56    inference(avatar_split_clause,[],[f287,f146,f140,f135,f130,f125,f120,f115,f289])).
% 0.22/0.56  fof(f287,plain,(
% 0.22/0.56    sK0 = k2_relset_1(sK1,sK0,sK3) | (~spl4_7 | ~spl4_8 | ~spl4_9 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 0.22/0.56    inference(subsumption_resolution,[],[f286,f127])).
% 0.22/0.56  fof(f286,plain,(
% 0.22/0.56    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_8 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 0.22/0.56    inference(subsumption_resolution,[],[f285,f122])).
% 0.22/0.56  fof(f285,plain,(
% 0.22/0.56    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_7 | ~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 0.22/0.56    inference(subsumption_resolution,[],[f284,f117])).
% 0.22/0.56  fof(f284,plain,(
% 0.22/0.56    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_12 | ~spl4_13)),
% 0.22/0.56    inference(subsumption_resolution,[],[f283,f142])).
% 0.22/0.56  fof(f283,plain,(
% 0.22/0.56    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_11 | ~spl4_13)),
% 0.22/0.56    inference(subsumption_resolution,[],[f282,f137])).
% 0.22/0.56  fof(f282,plain,(
% 0.22/0.56    sK0 = k2_relset_1(sK1,sK0,sK3) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | (~spl4_10 | ~spl4_13)),
% 0.22/0.56    inference(subsumption_resolution,[],[f279,f132])).
% 0.22/0.56  fof(f279,plain,(
% 0.22/0.56    sK0 = k2_relset_1(sK1,sK0,sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_2(sK3,sK1,sK0) | ~v1_funct_1(sK3) | ~spl4_13),
% 0.22/0.56    inference(resolution,[],[f278,f148])).
% 0.22/0.56  fof(f278,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_relat_1(X1)) | k2_relset_1(X0,X1,X2) = X1 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.56    inference(forward_demodulation,[],[f70,f72])).
% 0.22/0.56  fof(f70,plain,(
% 0.22/0.56    ( ! [X2,X0,X3,X1] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.22/0.56    inference(cnf_transformation,[],[f34])).
% 0.22/0.56  fof(f34,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (! [X3] : (k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.22/0.56    inference(flattening,[],[f33])).
% 0.22/0.56  fof(f33,plain,(
% 0.22/0.56    ! [X0,X1,X2] : (! [X3] : ((k2_relset_1(X0,X1,X2) = X1 | ~r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1))) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X3,X1,X0) | ~v1_funct_1(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.22/0.56    inference(ennf_transformation,[],[f13])).
% 0.22/0.56  fof(f13,axiom,(
% 0.22/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => (r2_relset_1(X1,X1,k1_partfun1(X1,X0,X0,X1,X3,X2),k6_partfun1(X1)) => k2_relset_1(X0,X1,X2) = X1)))),
% 0.22/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_funct_2)).
% 0.22/0.56  fof(f277,plain,(
% 0.22/0.56    spl4_24 | ~spl4_20),
% 0.22/0.56    inference(avatar_split_clause,[],[f276,f234,f272])).
% 0.22/0.56  fof(f234,plain,(
% 0.22/0.56    spl4_20 <=> k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2))),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_20])])).
% 0.22/0.56  fof(f276,plain,(
% 0.22/0.56    sK0 = k1_relat_1(sK2) | ~spl4_20),
% 0.22/0.56    inference(forward_demodulation,[],[f257,f76])).
% 0.22/0.56  fof(f76,plain,(
% 0.22/0.56    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.22/0.56    inference(cnf_transformation,[],[f3])).
% 0.22/0.56  fof(f257,plain,(
% 0.22/0.56    k1_relat_1(sK2) = k1_relat_1(k6_relat_1(sK0)) | ~spl4_20),
% 0.22/0.56    inference(superposition,[],[f76,f236])).
% 0.22/0.56  fof(f236,plain,(
% 0.22/0.56    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) | ~spl4_20),
% 0.22/0.56    inference(avatar_component_clause,[],[f234])).
% 0.22/0.56  fof(f253,plain,(
% 0.22/0.56    spl4_21 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 0.22/0.56    inference(avatar_split_clause,[],[f248,f140,f135,f130,f110,f100,f90,f250])).
% 0.22/0.56  fof(f90,plain,(
% 0.22/0.56    spl4_2 <=> k1_xboole_0 = sK1),
% 0.22/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_2])])).
% 0.22/0.56  fof(f248,plain,(
% 0.22/0.56    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 0.22/0.56    inference(subsumption_resolution,[],[f247,f142])).
% 0.22/0.56  fof(f247,plain,(
% 0.22/0.56    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 0.22/0.56    inference(subsumption_resolution,[],[f246,f137])).
% 0.22/0.56  fof(f246,plain,(
% 0.22/0.56    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 0.22/0.56    inference(subsumption_resolution,[],[f245,f132])).
% 0.22/0.56  fof(f245,plain,(
% 0.22/0.56    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 0.22/0.56    inference(subsumption_resolution,[],[f244,f102])).
% 0.22/0.56  fof(f244,plain,(
% 0.22/0.56    ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 0.22/0.56    inference(subsumption_resolution,[],[f243,f92])).
% 0.22/0.56  fof(f92,plain,(
% 0.22/0.56    k1_xboole_0 != sK1 | spl4_2),
% 0.22/0.56    inference(avatar_component_clause,[],[f90])).
% 1.47/0.56  fof(f243,plain,(
% 1.47/0.56    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.47/0.56    inference(trivial_inequality_removal,[],[f242])).
% 1.47/0.56  fof(f242,plain,(
% 1.47/0.56    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(sK1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.47/0.56    inference(superposition,[],[f213,f112])).
% 1.47/0.56  fof(f213,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k5_relat_1(k2_funct_1(X2),X2) = k6_relat_1(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.47/0.56    inference(forward_demodulation,[],[f57,f72])).
% 1.47/0.56  fof(f57,plain,(
% 1.47/0.56    ( ! [X2,X0,X1] : (k6_partfun1(X1) = k5_relat_1(k2_funct_1(X2),X2) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f22])).
% 1.47/0.56  fof(f241,plain,(
% 1.47/0.56    spl4_20 | ~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_19),
% 1.47/0.56    inference(avatar_split_clause,[],[f240,f222,f162,f140,f100,f234])).
% 1.47/0.56  fof(f222,plain,(
% 1.47/0.56    spl4_19 <=> k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_19])])).
% 1.47/0.56  fof(f240,plain,(
% 1.47/0.56    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) | (~spl4_4 | ~spl4_12 | ~spl4_15 | ~spl4_19)),
% 1.47/0.56    inference(subsumption_resolution,[],[f239,f164])).
% 1.47/0.56  fof(f239,plain,(
% 1.47/0.56    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_12 | ~spl4_19)),
% 1.47/0.56    inference(subsumption_resolution,[],[f238,f142])).
% 1.47/0.56  fof(f238,plain,(
% 1.47/0.56    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl4_4 | ~spl4_19)),
% 1.47/0.56    inference(subsumption_resolution,[],[f227,f102])).
% 1.47/0.56  fof(f227,plain,(
% 1.47/0.56    k6_relat_1(sK0) = k6_relat_1(k1_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl4_19),
% 1.47/0.56    inference(superposition,[],[f59,f224])).
% 1.47/0.56  fof(f224,plain,(
% 1.47/0.56    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl4_19),
% 1.47/0.56    inference(avatar_component_clause,[],[f222])).
% 1.47/0.56  fof(f225,plain,(
% 1.47/0.56    spl4_19 | spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12),
% 1.47/0.56    inference(avatar_split_clause,[],[f220,f140,f135,f130,f110,f100,f90,f222])).
% 1.47/0.56  fof(f220,plain,(
% 1.47/0.56    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11 | ~spl4_12)),
% 1.47/0.56    inference(subsumption_resolution,[],[f219,f142])).
% 1.47/0.56  fof(f219,plain,(
% 1.47/0.56    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10 | ~spl4_11)),
% 1.47/0.56    inference(subsumption_resolution,[],[f218,f137])).
% 1.47/0.56  fof(f218,plain,(
% 1.47/0.56    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6 | ~spl4_10)),
% 1.47/0.56    inference(subsumption_resolution,[],[f217,f132])).
% 1.47/0.56  fof(f217,plain,(
% 1.47/0.56    k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_4 | ~spl4_6)),
% 1.47/0.56    inference(subsumption_resolution,[],[f216,f102])).
% 1.47/0.56  fof(f216,plain,(
% 1.47/0.56    ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | (spl4_2 | ~spl4_6)),
% 1.47/0.56    inference(subsumption_resolution,[],[f215,f92])).
% 1.47/0.56  fof(f215,plain,(
% 1.47/0.56    k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.47/0.56    inference(trivial_inequality_removal,[],[f214])).
% 1.47/0.56  fof(f214,plain,(
% 1.47/0.56    sK1 != sK1 | k1_xboole_0 = sK1 | ~v2_funct_1(sK2) | k6_relat_1(sK0) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_2(sK2,sK0,sK1) | ~v1_funct_1(sK2) | ~spl4_6),
% 1.47/0.56    inference(superposition,[],[f212,f112])).
% 1.47/0.56  fof(f202,plain,(
% 1.47/0.56    spl4_18 | ~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13),
% 1.47/0.56    inference(avatar_split_clause,[],[f197,f146,f140,f130,f125,f115,f199])).
% 1.47/0.56  fof(f197,plain,(
% 1.47/0.56    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_12 | ~spl4_13)),
% 1.47/0.56    inference(subsumption_resolution,[],[f196,f142])).
% 1.47/0.56  fof(f196,plain,(
% 1.47/0.56    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_10 | ~spl4_13)),
% 1.47/0.56    inference(subsumption_resolution,[],[f195,f132])).
% 1.47/0.56  fof(f195,plain,(
% 1.47/0.56    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_9 | ~spl4_13)),
% 1.47/0.56    inference(subsumption_resolution,[],[f194,f127])).
% 1.47/0.56  fof(f194,plain,(
% 1.47/0.56    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | (~spl4_7 | ~spl4_13)),
% 1.47/0.56    inference(subsumption_resolution,[],[f191,f117])).
% 1.47/0.56  fof(f191,plain,(
% 1.47/0.56    r2_relset_1(sK0,sK0,k5_relat_1(sK2,sK3),k6_relat_1(sK0)) | ~m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~v1_funct_1(sK2) | ~spl4_13),
% 1.47/0.56    inference(superposition,[],[f148,f75])).
% 1.47/0.56  fof(f165,plain,(
% 1.47/0.56    spl4_15 | ~spl4_10),
% 1.47/0.56    inference(avatar_split_clause,[],[f160,f130,f162])).
% 1.47/0.56  fof(f160,plain,(
% 1.47/0.56    v1_relat_1(sK2) | ~spl4_10),
% 1.47/0.56    inference(subsumption_resolution,[],[f152,f79])).
% 1.47/0.56  fof(f79,plain,(
% 1.47/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.47/0.56    inference(cnf_transformation,[],[f2])).
% 1.47/0.56  fof(f2,axiom,(
% 1.47/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.47/0.56  fof(f152,plain,(
% 1.47/0.56    v1_relat_1(sK2) | ~v1_relat_1(k2_zfmisc_1(sK0,sK1)) | ~spl4_10),
% 1.47/0.56    inference(resolution,[],[f78,f132])).
% 1.47/0.56  fof(f78,plain,(
% 1.47/0.56    ( ! [X0,X1] : (~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1) | ~v1_relat_1(X0)) )),
% 1.47/0.56    inference(cnf_transformation,[],[f39])).
% 1.47/0.56  fof(f39,plain,(
% 1.47/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.47/0.56    inference(ennf_transformation,[],[f1])).
% 1.47/0.56  fof(f1,axiom,(
% 1.47/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.47/0.56  fof(f159,plain,(
% 1.47/0.56    spl4_14 | ~spl4_7),
% 1.47/0.56    inference(avatar_split_clause,[],[f154,f115,f156])).
% 1.47/0.56  fof(f154,plain,(
% 1.47/0.56    v1_relat_1(sK3) | ~spl4_7),
% 1.47/0.56    inference(subsumption_resolution,[],[f151,f79])).
% 1.47/0.56  fof(f151,plain,(
% 1.47/0.56    v1_relat_1(sK3) | ~v1_relat_1(k2_zfmisc_1(sK1,sK0)) | ~spl4_7),
% 1.47/0.56    inference(resolution,[],[f78,f117])).
% 1.47/0.56  fof(f149,plain,(
% 1.47/0.56    spl4_13 | ~spl4_5),
% 1.47/0.56    inference(avatar_split_clause,[],[f144,f105,f146])).
% 1.47/0.56  fof(f105,plain,(
% 1.47/0.56    spl4_5 <=> r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.47/0.56    introduced(avatar_definition,[new_symbols(naming,[spl4_5])])).
% 1.47/0.56  fof(f144,plain,(
% 1.47/0.56    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_relat_1(sK0)) | ~spl4_5),
% 1.47/0.56    inference(backward_demodulation,[],[f107,f72])).
% 1.47/0.56  fof(f107,plain,(
% 1.47/0.56    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) | ~spl4_5),
% 1.47/0.56    inference(avatar_component_clause,[],[f105])).
% 1.47/0.56  fof(f143,plain,(
% 1.47/0.56    spl4_12),
% 1.47/0.56    inference(avatar_split_clause,[],[f44,f140])).
% 1.47/0.56  fof(f44,plain,(
% 1.47/0.56    v1_funct_1(sK2)),
% 1.47/0.56    inference(cnf_transformation,[],[f42])).
% 1.47/0.56  fof(f42,plain,(
% 1.47/0.56    (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2)),
% 1.47/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3])],[f20,f41,f40])).
% 1.47/0.56  fof(f40,plain,(
% 1.47/0.56    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) & v1_funct_2(sK2,sK0,sK1) & v1_funct_1(sK2))),
% 1.47/0.56    introduced(choice_axiom,[])).
% 1.47/0.56  fof(f41,plain,(
% 1.47/0.56    ? [X3] : (k2_funct_1(sK2) != X3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,X3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(X3,sK1,sK0) & v1_funct_1(X3)) => (k2_funct_1(sK2) != sK3 & k1_xboole_0 != sK1 & k1_xboole_0 != sK0 & v2_funct_1(sK2) & r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0)) & sK1 = k2_relset_1(sK0,sK1,sK2) & m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) & v1_funct_2(sK3,sK1,sK0) & v1_funct_1(sK3))),
% 1.47/0.56    introduced(choice_axiom,[])).
% 1.47/0.56  fof(f20,plain,(
% 1.47/0.56    ? [X0,X1,X2] : (? [X3] : (k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0 & v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1 & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 1.47/0.56    inference(flattening,[],[f19])).
% 1.47/0.56  fof(f19,plain,(
% 1.47/0.56    ? [X0,X1,X2] : (? [X3] : (((k2_funct_1(X2) != X3 & k1_xboole_0 != X1 & k1_xboole_0 != X0) & (v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1)) & (m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 1.47/0.56    inference(ennf_transformation,[],[f17])).
% 1.47/0.56  fof(f17,negated_conjecture,(
% 1.47/0.56    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.47/0.56    inference(negated_conjecture,[],[f16])).
% 1.47/0.56  fof(f16,conjecture,(
% 1.47/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(X3,X1,X0) & v1_funct_1(X3)) => ((v2_funct_1(X2) & r2_relset_1(X0,X0,k1_partfun1(X0,X1,X1,X0,X2,X3),k6_partfun1(X0)) & k2_relset_1(X0,X1,X2) = X1) => (k2_funct_1(X2) = X3 | k1_xboole_0 = X1 | k1_xboole_0 = X0))))),
% 1.47/0.56    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_funct_2)).
% 1.47/0.56  fof(f138,plain,(
% 1.47/0.56    spl4_11),
% 1.47/0.56    inference(avatar_split_clause,[],[f45,f135])).
% 1.47/0.56  fof(f45,plain,(
% 1.47/0.56    v1_funct_2(sK2,sK0,sK1)),
% 1.47/0.56    inference(cnf_transformation,[],[f42])).
% 1.47/0.56  fof(f133,plain,(
% 1.47/0.56    spl4_10),
% 1.47/0.56    inference(avatar_split_clause,[],[f46,f130])).
% 1.47/0.56  fof(f46,plain,(
% 1.47/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 1.47/0.56    inference(cnf_transformation,[],[f42])).
% 1.47/0.56  fof(f128,plain,(
% 1.47/0.56    spl4_9),
% 1.47/0.56    inference(avatar_split_clause,[],[f47,f125])).
% 1.47/0.56  fof(f47,plain,(
% 1.47/0.56    v1_funct_1(sK3)),
% 1.47/0.56    inference(cnf_transformation,[],[f42])).
% 1.47/0.56  % (17541)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_91 on theBenchmark
% 1.47/0.56  fof(f123,plain,(
% 1.47/0.56    spl4_8),
% 1.47/0.56    inference(avatar_split_clause,[],[f48,f120])).
% 1.47/0.56  fof(f48,plain,(
% 1.47/0.56    v1_funct_2(sK3,sK1,sK0)),
% 1.47/0.56    inference(cnf_transformation,[],[f42])).
% 1.47/0.56  fof(f118,plain,(
% 1.47/0.56    spl4_7),
% 1.47/0.56    inference(avatar_split_clause,[],[f49,f115])).
% 1.47/0.56  fof(f49,plain,(
% 1.47/0.56    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 1.47/0.56    inference(cnf_transformation,[],[f42])).
% 1.47/0.56  fof(f113,plain,(
% 1.47/0.56    spl4_6),
% 1.47/0.56    inference(avatar_split_clause,[],[f50,f110])).
% 1.47/0.56  fof(f50,plain,(
% 1.47/0.56    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 1.47/0.56    inference(cnf_transformation,[],[f42])).
% 1.47/0.57  fof(f108,plain,(
% 1.47/0.57    spl4_5),
% 1.47/0.57    inference(avatar_split_clause,[],[f51,f105])).
% 1.47/0.57  fof(f51,plain,(
% 1.47/0.57    r2_relset_1(sK0,sK0,k1_partfun1(sK0,sK1,sK1,sK0,sK2,sK3),k6_partfun1(sK0))),
% 1.47/0.57    inference(cnf_transformation,[],[f42])).
% 1.47/0.57  fof(f103,plain,(
% 1.47/0.57    spl4_4),
% 1.47/0.57    inference(avatar_split_clause,[],[f52,f100])).
% 1.47/0.57  fof(f52,plain,(
% 1.47/0.57    v2_funct_1(sK2)),
% 1.47/0.57    inference(cnf_transformation,[],[f42])).
% 1.47/0.57  fof(f98,plain,(
% 1.47/0.57    ~spl4_3),
% 1.47/0.57    inference(avatar_split_clause,[],[f53,f95])).
% 1.47/0.57  fof(f53,plain,(
% 1.47/0.57    k1_xboole_0 != sK0),
% 1.47/0.57    inference(cnf_transformation,[],[f42])).
% 1.47/0.57  fof(f93,plain,(
% 1.47/0.57    ~spl4_2),
% 1.47/0.57    inference(avatar_split_clause,[],[f54,f90])).
% 1.47/0.57  fof(f54,plain,(
% 1.47/0.57    k1_xboole_0 != sK1),
% 1.47/0.57    inference(cnf_transformation,[],[f42])).
% 1.47/0.57  fof(f88,plain,(
% 1.47/0.57    ~spl4_1),
% 1.47/0.57    inference(avatar_split_clause,[],[f55,f85])).
% 1.47/0.57  fof(f55,plain,(
% 1.47/0.57    k2_funct_1(sK2) != sK3),
% 1.47/0.57    inference(cnf_transformation,[],[f42])).
% 1.47/0.57  % SZS output end Proof for theBenchmark
% 1.47/0.57  % (17537)------------------------------
% 1.47/0.57  % (17537)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.47/0.57  % (17537)Termination reason: Refutation
% 1.47/0.57  
% 1.47/0.57  % (17537)Memory used [KB]: 6908
% 1.47/0.57  % (17537)Time elapsed: 0.131 s
% 1.47/0.57  % (17537)------------------------------
% 1.47/0.57  % (17537)------------------------------
% 1.47/0.57  % (17539)dis+1010_4_acc=on:afr=on:afp=1000:afq=2.0:anc=none:bd=off:bs=unit_only:bsr=on:ccuc=small_ones:cond=fast:fsr=off:gs=on:gsem=off:lcm=reverse:lma=on:nm=64:nwc=2.5:nicw=on:sd=3:ss=axioms:st=3.0:sac=on:urr=ec_only:updr=off:uhcvi=on_83 on theBenchmark
% 1.47/0.57  % (17515)Success in time 0.201 s
%------------------------------------------------------------------------------
