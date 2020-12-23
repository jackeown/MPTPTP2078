%------------------------------------------------------------------------------
% File       : Vampire---4.4
% Problem    : funct_2__t33_funct_2.p : TPTP v0.0.0. Released v0.0.0.
% Transform  : none
% Format     : tptp:raw
% Command    : vampire --mode casc -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 300s
% DateTime   : Fri Oct 11 10:36:44 EDT 2019

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  252 ( 512 expanded)
%              Number of leaves         :   56 ( 221 expanded)
%              Depth                    :   11
%              Number of atoms          :  778 (1640 expanded)
%              Number of equality atoms :  118 ( 235 expanded)
%              Maximal formula depth    :   14 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f3186,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f115,f119,f131,f135,f139,f147,f151,f191,f195,f199,f205,f209,f219,f227,f250,f255,f261,f288,f297,f307,f311,f351,f358,f411,f684,f777,f915,f943,f964,f1563,f1585,f1670,f1715,f1733,f1797,f2576,f2577,f3089,f3168,f3184,f3185])).

fof(f3185,plain,
    ( k1_xboole_0 != k1_relat_1(sK4)
    | k1_xboole_0 != sK1
    | k1_relat_1(sK4) = sK1 ),
    introduced(theory_axiom,[])).

fof(f3184,plain,
    ( spl6_118
    | ~ spl6_408
    | ~ spl6_632
    | ~ spl6_678 ),
    inference(avatar_split_clause,[],[f3169,f3087,f2637,f1713,f457])).

fof(f457,plain,
    ( spl6_118
  <=> k1_xboole_0 = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_118])])).

fof(f1713,plain,
    ( spl6_408
  <=> v1_funct_2(sK4,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_408])])).

fof(f2637,plain,
    ( spl6_632
  <=> k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_632])])).

fof(f3087,plain,
    ( spl6_678
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_678])])).

fof(f3169,plain,
    ( k1_xboole_0 = k1_relat_1(sK4)
    | ~ spl6_408
    | ~ spl6_632
    | ~ spl6_678 ),
    inference(forward_demodulation,[],[f2638,f3126])).

fof(f3126,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)
    | ~ spl6_408
    | ~ spl6_678 ),
    inference(subsumption_resolution,[],[f3105,f1714])).

fof(f1714,plain,
    ( v1_funct_2(sK4,k1_xboole_0,k1_xboole_0)
    | ~ spl6_408 ),
    inference(avatar_component_clause,[],[f1713])).

fof(f3105,plain,
    ( k1_xboole_0 = k1_relset_1(k1_xboole_0,k1_xboole_0,sK4)
    | ~ v1_funct_2(sK4,k1_xboole_0,k1_xboole_0)
    | ~ spl6_678 ),
    inference(resolution,[],[f3088,f107])).

fof(f107,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
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
    inference(flattening,[],[f43])).

fof(f43,plain,(
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
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t33_funct_2.p',d1_funct_2)).

fof(f3088,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_678 ),
    inference(avatar_component_clause,[],[f3087])).

fof(f2638,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_relat_1(sK4)
    | ~ spl6_632 ),
    inference(avatar_component_clause,[],[f2637])).

fof(f3168,plain,
    ( spl6_632
    | ~ spl6_64
    | ~ spl6_82
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f2756,f382,f356,f309,f2637])).

fof(f309,plain,
    ( spl6_64
  <=> k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f356,plain,
    ( spl6_82
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_82])])).

fof(f382,plain,
    ( spl6_92
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_92])])).

fof(f2756,plain,
    ( k1_relset_1(k1_xboole_0,k1_xboole_0,sK4) = k1_relat_1(sK4)
    | ~ spl6_64
    | ~ spl6_82
    | ~ spl6_92 ),
    inference(forward_demodulation,[],[f665,f357])).

fof(f357,plain,
    ( k1_xboole_0 = sK2
    | ~ spl6_82 ),
    inference(avatar_component_clause,[],[f356])).

fof(f665,plain,
    ( k1_relset_1(k1_xboole_0,sK2,sK4) = k1_relat_1(sK4)
    | ~ spl6_64
    | ~ spl6_92 ),
    inference(superposition,[],[f310,f383])).

fof(f383,plain,
    ( k1_xboole_0 = sK1
    | ~ spl6_92 ),
    inference(avatar_component_clause,[],[f382])).

fof(f310,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4)
    | ~ spl6_64 ),
    inference(avatar_component_clause,[],[f309])).

fof(f3089,plain,
    ( spl6_678
    | ~ spl6_16
    | ~ spl6_82
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f2762,f382,f356,f145,f3087])).

fof(f145,plain,
    ( spl6_16
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f2762,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_xboole_0)))
    | ~ spl6_16
    | ~ spl6_82
    | ~ spl6_92 ),
    inference(forward_demodulation,[],[f472,f357])).

fof(f472,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK2)))
    | ~ spl6_16
    | ~ spl6_92 ),
    inference(superposition,[],[f146,f383])).

fof(f146,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2)))
    | ~ spl6_16 ),
    inference(avatar_component_clause,[],[f145])).

fof(f2577,plain,
    ( k1_xboole_0 != sK4
    | k1_xboole_0 != k2_relat_1(k5_relat_1(sK3,k1_xboole_0))
    | k1_xboole_0 != sK2
    | k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    introduced(theory_axiom,[])).

fof(f2576,plain,
    ( spl6_594
    | ~ spl6_20
    | ~ spl6_24
    | ~ spl6_30
    | ~ spl6_34
    | ~ spl6_62
    | ~ spl6_82
    | ~ spl6_424 ),
    inference(avatar_split_clause,[],[f2044,f1795,f356,f305,f225,f217,f197,f189,f2574])).

fof(f2574,plain,
    ( spl6_594
  <=> k1_xboole_0 = k2_relat_1(k5_relat_1(sK3,k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_594])])).

fof(f189,plain,
    ( spl6_20
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f197,plain,
    ( spl6_24
  <=> v1_relat_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f217,plain,
    ( spl6_30
  <=> k2_relat_1(sK4) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f225,plain,
    ( spl6_34
  <=> k2_relat_1(sK3) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f305,plain,
    ( spl6_62
  <=> r1_tarski(k1_relat_1(sK4),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f1795,plain,
    ( spl6_424
  <=> k1_xboole_0 = sK4 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_424])])).

fof(f2044,plain,
    ( k1_xboole_0 = k2_relat_1(k5_relat_1(sK3,k1_xboole_0))
    | ~ spl6_20
    | ~ spl6_24
    | ~ spl6_30
    | ~ spl6_34
    | ~ spl6_62
    | ~ spl6_82
    | ~ spl6_424 ),
    inference(forward_demodulation,[],[f2043,f1927])).

fof(f1927,plain,
    ( k1_xboole_0 = k2_relat_1(k1_xboole_0)
    | ~ spl6_30
    | ~ spl6_82
    | ~ spl6_424 ),
    inference(forward_demodulation,[],[f1846,f357])).

fof(f1846,plain,
    ( k2_relat_1(k1_xboole_0) = sK2
    | ~ spl6_30
    | ~ spl6_424 ),
    inference(superposition,[],[f218,f1796])).

fof(f1796,plain,
    ( k1_xboole_0 = sK4
    | ~ spl6_424 ),
    inference(avatar_component_clause,[],[f1795])).

fof(f218,plain,
    ( k2_relat_1(sK4) = sK2
    | ~ spl6_30 ),
    inference(avatar_component_clause,[],[f217])).

fof(f2043,plain,
    ( k2_relat_1(k1_xboole_0) = k2_relat_1(k5_relat_1(sK3,k1_xboole_0))
    | ~ spl6_20
    | ~ spl6_24
    | ~ spl6_34
    | ~ spl6_62
    | ~ spl6_424 ),
    inference(forward_demodulation,[],[f2042,f1796])).

fof(f2042,plain,
    ( k2_relat_1(sK4) = k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl6_20
    | ~ spl6_24
    | ~ spl6_34
    | ~ spl6_62 ),
    inference(subsumption_resolution,[],[f2038,f190])).

fof(f190,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_20 ),
    inference(avatar_component_clause,[],[f189])).

fof(f2038,plain,
    ( ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) = k2_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl6_24
    | ~ spl6_34
    | ~ spl6_62 ),
    inference(resolution,[],[f278,f306])).

fof(f306,plain,
    ( r1_tarski(k1_relat_1(sK4),sK1)
    | ~ spl6_62 ),
    inference(avatar_component_clause,[],[f305])).

fof(f278,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(X0),sK1)
        | ~ v1_relat_1(X0)
        | k2_relat_1(X0) = k2_relat_1(k5_relat_1(sK3,X0)) )
    | ~ spl6_24
    | ~ spl6_34 ),
    inference(subsumption_resolution,[],[f276,f198])).

fof(f198,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_24 ),
    inference(avatar_component_clause,[],[f197])).

fof(f276,plain,
    ( ! [X0] :
        ( ~ r1_tarski(k1_relat_1(X0),sK1)
        | ~ v1_relat_1(sK3)
        | ~ v1_relat_1(X0)
        | k2_relat_1(X0) = k2_relat_1(k5_relat_1(sK3,X0)) )
    | ~ spl6_34 ),
    inference(superposition,[],[f94,f226])).

fof(f226,plain,
    ( k2_relat_1(sK3) = sK1
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f225])).

fof(f94,plain,(
    ! [X0,X1] :
      ( ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f52])).

fof(f52,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0))
          | ~ r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
          | ~ v1_relat_1(X1) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f24])).

fof(f24,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( v1_relat_1(X1)
         => ( r1_tarski(k1_relat_1(X0),k2_relat_1(X1))
           => k2_relat_1(X0) = k2_relat_1(k5_relat_1(X1,X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t33_funct_2.p',t47_relat_1)).

fof(f1797,plain,
    ( spl6_424
    | spl6_92
    | ~ spl6_394
    | ~ spl6_412 ),
    inference(avatar_split_clause,[],[f1754,f1731,f1668,f382,f1795])).

fof(f1668,plain,
    ( spl6_394
  <=> v1_funct_2(sK4,sK1,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_394])])).

fof(f1731,plain,
    ( spl6_412
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_412])])).

fof(f1754,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK4
    | ~ spl6_394
    | ~ spl6_412 ),
    inference(subsumption_resolution,[],[f1734,f1669])).

fof(f1669,plain,
    ( v1_funct_2(sK4,sK1,k1_xboole_0)
    | ~ spl6_394 ),
    inference(avatar_component_clause,[],[f1668])).

fof(f1734,plain,
    ( k1_xboole_0 = sK1
    | k1_xboole_0 = sK4
    | ~ v1_funct_2(sK4,sK1,k1_xboole_0)
    | ~ spl6_412 ),
    inference(resolution,[],[f1732,f109])).

fof(f109,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f1732,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl6_412 ),
    inference(avatar_component_clause,[],[f1731])).

fof(f1733,plain,
    ( spl6_412
    | ~ spl6_16
    | ~ spl6_82 ),
    inference(avatar_split_clause,[],[f371,f356,f145,f1731])).

fof(f371,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,k1_xboole_0)))
    | ~ spl6_16
    | ~ spl6_82 ),
    inference(superposition,[],[f146,f357])).

fof(f1715,plain,
    ( spl6_408
    | ~ spl6_82
    | ~ spl6_152 ),
    inference(avatar_split_clause,[],[f1624,f682,f356,f1713])).

fof(f682,plain,
    ( spl6_152
  <=> v1_funct_2(sK4,k1_xboole_0,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_152])])).

fof(f1624,plain,
    ( v1_funct_2(sK4,k1_xboole_0,k1_xboole_0)
    | ~ spl6_82
    | ~ spl6_152 ),
    inference(superposition,[],[f683,f357])).

fof(f683,plain,
    ( v1_funct_2(sK4,k1_xboole_0,sK2)
    | ~ spl6_152 ),
    inference(avatar_component_clause,[],[f682])).

fof(f1670,plain,
    ( spl6_394
    | ~ spl6_12
    | ~ spl6_82 ),
    inference(avatar_split_clause,[],[f370,f356,f137,f1668])).

fof(f137,plain,
    ( spl6_12
  <=> v1_funct_2(sK4,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f370,plain,
    ( v1_funct_2(sK4,sK1,k1_xboole_0)
    | ~ spl6_12
    | ~ spl6_82 ),
    inference(superposition,[],[f138,f357])).

fof(f138,plain,
    ( v1_funct_2(sK4,sK1,sK2)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f137])).

fof(f1585,plain,
    ( ~ spl6_78
    | ~ spl6_192
    | spl6_213
    | ~ spl6_372 ),
    inference(avatar_contradiction_clause,[],[f1584])).

fof(f1584,plain,
    ( $false
    | ~ spl6_78
    | ~ spl6_192
    | ~ spl6_213
    | ~ spl6_372 ),
    inference(subsumption_resolution,[],[f1583,f963])).

fof(f963,plain,
    ( ~ v2_funct_2(k5_relat_1(sK3,sK4),sK2)
    | ~ spl6_213 ),
    inference(avatar_component_clause,[],[f962])).

fof(f962,plain,
    ( spl6_213
  <=> ~ v2_funct_2(k5_relat_1(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_213])])).

fof(f1583,plain,
    ( v2_funct_2(k5_relat_1(sK3,sK4),sK2)
    | ~ spl6_78
    | ~ spl6_192
    | ~ spl6_372 ),
    inference(forward_demodulation,[],[f1582,f1562])).

fof(f1562,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2
    | ~ spl6_372 ),
    inference(avatar_component_clause,[],[f1561])).

fof(f1561,plain,
    ( spl6_372
  <=> k2_relat_1(k5_relat_1(sK3,sK4)) = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_372])])).

fof(f1582,plain,
    ( v2_funct_2(k5_relat_1(sK3,sK4),k2_relat_1(k5_relat_1(sK3,sK4)))
    | ~ spl6_78
    | ~ spl6_192
    | ~ spl6_372 ),
    inference(subsumption_resolution,[],[f1581,f350])).

fof(f350,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl6_78 ),
    inference(avatar_component_clause,[],[f349])).

fof(f349,plain,
    ( spl6_78
  <=> v1_relat_1(k5_relat_1(sK3,sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_78])])).

fof(f1581,plain,
    ( ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | v2_funct_2(k5_relat_1(sK3,sK4),k2_relat_1(k5_relat_1(sK3,sK4)))
    | ~ spl6_192
    | ~ spl6_372 ),
    inference(subsumption_resolution,[],[f1577,f914])).

fof(f914,plain,
    ( v5_relat_1(k5_relat_1(sK3,sK4),sK2)
    | ~ spl6_192 ),
    inference(avatar_component_clause,[],[f913])).

fof(f913,plain,
    ( spl6_192
  <=> v5_relat_1(k5_relat_1(sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_192])])).

fof(f1577,plain,
    ( ~ v5_relat_1(k5_relat_1(sK3,sK4),sK2)
    | ~ v1_relat_1(k5_relat_1(sK3,sK4))
    | v2_funct_2(k5_relat_1(sK3,sK4),k2_relat_1(k5_relat_1(sK3,sK4)))
    | ~ spl6_372 ),
    inference(superposition,[],[f106,f1562])).

fof(f106,plain,(
    ! [X1] :
      ( ~ v5_relat_1(X1,k2_relat_1(X1))
      | ~ v1_relat_1(X1)
      | v2_funct_2(X1,k2_relat_1(X1)) ) ),
    inference(equality_resolution,[],[f80])).

fof(f80,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v5_relat_1(X1,X0)
      | k2_relat_1(X1) != X0
      | v2_funct_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 )
      | ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( ( v5_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v2_funct_2(X1,X0)
      <=> k2_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t33_funct_2.p',d3_funct_2)).

fof(f1563,plain,
    ( spl6_372
    | ~ spl6_20
    | ~ spl6_24
    | ~ spl6_30
    | ~ spl6_34
    | ~ spl6_48
    | ~ spl6_104 ),
    inference(avatar_split_clause,[],[f1559,f407,f259,f225,f217,f197,f189,f1561])).

fof(f259,plain,
    ( spl6_48
  <=> r1_tarski(sK1,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f407,plain,
    ( spl6_104
  <=> k1_relat_1(sK4) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_104])])).

fof(f1559,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2
    | ~ spl6_20
    | ~ spl6_24
    | ~ spl6_30
    | ~ spl6_34
    | ~ spl6_48
    | ~ spl6_104 ),
    inference(subsumption_resolution,[],[f1558,f198])).

fof(f1558,plain,
    ( k2_relat_1(k5_relat_1(sK3,sK4)) = sK2
    | ~ v1_relat_1(sK3)
    | ~ spl6_20
    | ~ spl6_30
    | ~ spl6_34
    | ~ spl6_48
    | ~ spl6_104 ),
    inference(subsumption_resolution,[],[f1556,f260])).

fof(f260,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl6_48 ),
    inference(avatar_component_clause,[],[f259])).

fof(f1556,plain,
    ( ~ r1_tarski(sK1,sK1)
    | k2_relat_1(k5_relat_1(sK3,sK4)) = sK2
    | ~ v1_relat_1(sK3)
    | ~ spl6_20
    | ~ spl6_30
    | ~ spl6_34
    | ~ spl6_104 ),
    inference(superposition,[],[f517,f226])).

fof(f517,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,k2_relat_1(X0))
        | k2_relat_1(k5_relat_1(X0,sK4)) = sK2
        | ~ v1_relat_1(X0) )
    | ~ spl6_20
    | ~ spl6_30
    | ~ spl6_104 ),
    inference(forward_demodulation,[],[f516,f218])).

fof(f516,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | k2_relat_1(sK4) = k2_relat_1(k5_relat_1(X0,sK4)) )
    | ~ spl6_20
    | ~ spl6_104 ),
    inference(subsumption_resolution,[],[f515,f190])).

fof(f515,plain,
    ( ! [X0] :
        ( ~ r1_tarski(sK1,k2_relat_1(X0))
        | ~ v1_relat_1(X0)
        | ~ v1_relat_1(sK4)
        | k2_relat_1(sK4) = k2_relat_1(k5_relat_1(X0,sK4)) )
    | ~ spl6_104 ),
    inference(superposition,[],[f94,f408])).

fof(f408,plain,
    ( k1_relat_1(sK4) = sK1
    | ~ spl6_104 ),
    inference(avatar_component_clause,[],[f407])).

fof(f964,plain,
    ( ~ spl6_213
    | spl6_23
    | ~ spl6_202 ),
    inference(avatar_split_clause,[],[f960,f941,f193,f962])).

fof(f193,plain,
    ( spl6_23
  <=> ~ v2_funct_2(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f941,plain,
    ( spl6_202
  <=> k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_202])])).

fof(f960,plain,
    ( ~ v2_funct_2(k5_relat_1(sK3,sK4),sK2)
    | ~ spl6_23
    | ~ spl6_202 ),
    inference(superposition,[],[f194,f942])).

fof(f942,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl6_202 ),
    inference(avatar_component_clause,[],[f941])).

fof(f194,plain,
    ( ~ v2_funct_2(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),sK2)
    | ~ spl6_23 ),
    inference(avatar_component_clause,[],[f193])).

fof(f943,plain,
    ( spl6_202
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_16
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f539,f149,f145,f117,f113,f941])).

fof(f113,plain,
    ( spl6_0
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_0])])).

fof(f117,plain,
    ( spl6_2
  <=> v1_funct_1(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f149,plain,
    ( spl6_18
  <=> m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f539,plain,
    ( k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_16
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f536,f114])).

fof(f114,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_0 ),
    inference(avatar_component_clause,[],[f113])).

fof(f536,plain,
    ( ~ v1_funct_1(sK4)
    | k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4) = k5_relat_1(sK3,sK4)
    | ~ spl6_2
    | ~ spl6_16
    | ~ spl6_18 ),
    inference(resolution,[],[f185,f146])).

fof(f185,plain,
    ( ! [X6,X8,X7] :
        ( ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | ~ v1_funct_1(X6)
        | k1_partfun1(sK0,sK1,X7,X8,sK3,X6) = k5_relat_1(sK3,X6) )
    | ~ spl6_2
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f172,f118])).

fof(f118,plain,
    ( v1_funct_1(sK3)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f117])).

fof(f172,plain,
    ( ! [X6,X8,X7] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X6)
        | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(X7,X8)))
        | k1_partfun1(sK0,sK1,X7,X8,sK3,X6) = k5_relat_1(sK3,X6) )
    | ~ spl6_18 ),
    inference(resolution,[],[f150,f79])).

fof(f79,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
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
    file('/export/starexec/sandbox2/benchmark/funct_2__t33_funct_2.p',redefinition_k1_partfun1)).

fof(f150,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f149])).

fof(f915,plain,
    ( spl6_192
    | ~ spl6_184 ),
    inference(avatar_split_clause,[],[f883,f775,f913])).

fof(f775,plain,
    ( spl6_184
  <=> m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_184])])).

fof(f883,plain,
    ( v5_relat_1(k5_relat_1(sK3,sK4),sK2)
    | ~ spl6_184 ),
    inference(resolution,[],[f776,f96])).

fof(f96,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v5_relat_1(X2,X1) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2] :
      ( v5_relat_1(X2,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v5_relat_1(X2,X1) ) ),
    inference(pure_predicate_removal,[],[f31])).

fof(f31,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t33_funct_2.p',cc2_relset_1)).

fof(f776,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_184 ),
    inference(avatar_component_clause,[],[f775])).

fof(f777,plain,
    ( spl6_184
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_16
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f572,f149,f145,f117,f113,f775])).

fof(f572,plain,
    ( m1_subset_1(k5_relat_1(sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_16
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f571,f539])).

fof(f571,plain,
    ( m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_0
    | ~ spl6_2
    | ~ spl6_16
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f567,f114])).

fof(f567,plain,
    ( ~ v1_funct_1(sK4)
    | m1_subset_1(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),k1_zfmisc_1(k2_zfmisc_1(sK0,sK2)))
    | ~ spl6_2
    | ~ spl6_16
    | ~ spl6_18 ),
    inference(resolution,[],[f184,f146])).

fof(f184,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | ~ v1_funct_1(X3)
        | m1_subset_1(k1_partfun1(sK0,sK1,X4,X5,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,X5))) )
    | ~ spl6_2
    | ~ spl6_18 ),
    inference(subsumption_resolution,[],[f171,f118])).

fof(f171,plain,
    ( ! [X4,X5,X3] :
        ( ~ v1_funct_1(sK3)
        | ~ v1_funct_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))
        | m1_subset_1(k1_partfun1(sK0,sK1,X4,X5,sK3,X3),k1_zfmisc_1(k2_zfmisc_1(sK0,X5))) )
    | ~ spl6_18 ),
    inference(resolution,[],[f150,f78])).

fof(f78,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3))) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => ( m1_subset_1(k1_partfun1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(X0,X3)))
        & v1_funct_1(k1_partfun1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t33_funct_2.p',dt_k1_partfun1)).

fof(f684,plain,
    ( spl6_152
    | ~ spl6_12
    | ~ spl6_92 ),
    inference(avatar_split_clause,[],[f470,f382,f137,f682])).

fof(f470,plain,
    ( v1_funct_2(sK4,k1_xboole_0,sK2)
    | ~ spl6_12
    | ~ spl6_92 ),
    inference(superposition,[],[f138,f383])).

fof(f411,plain,
    ( spl6_104
    | ~ spl6_64
    | ~ spl6_80 ),
    inference(avatar_split_clause,[],[f409,f353,f309,f407])).

fof(f353,plain,
    ( spl6_80
  <=> k1_relset_1(sK1,sK2,sK4) = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_80])])).

fof(f409,plain,
    ( k1_relat_1(sK4) = sK1
    | ~ spl6_64
    | ~ spl6_80 ),
    inference(superposition,[],[f354,f310])).

fof(f354,plain,
    ( k1_relset_1(sK1,sK2,sK4) = sK1
    | ~ spl6_80 ),
    inference(avatar_component_clause,[],[f353])).

fof(f358,plain,
    ( spl6_80
    | spl6_82
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f168,f145,f137,f356,f353])).

fof(f168,plain,
    ( k1_xboole_0 = sK2
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | ~ spl6_12
    | ~ spl6_16 ),
    inference(subsumption_resolution,[],[f156,f138])).

fof(f156,plain,
    ( k1_xboole_0 = sK2
    | k1_relset_1(sK1,sK2,sK4) = sK1
    | ~ v1_funct_2(sK4,sK1,sK2)
    | ~ spl6_16 ),
    inference(resolution,[],[f146,f88])).

fof(f88,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f351,plain,
    ( spl6_78
    | ~ spl6_20
    | ~ spl6_24 ),
    inference(avatar_split_clause,[],[f344,f197,f189,f349])).

fof(f344,plain,
    ( v1_relat_1(k5_relat_1(sK3,sK4))
    | ~ spl6_20
    | ~ spl6_24 ),
    inference(resolution,[],[f201,f190])).

fof(f201,plain,
    ( ! [X0] :
        ( ~ v1_relat_1(X0)
        | v1_relat_1(k5_relat_1(sK3,X0)) )
    | ~ spl6_24 ),
    inference(resolution,[],[f198,f93])).

fof(f93,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ v1_relat_1(X1)
      | v1_relat_1(k5_relat_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1] :
      ( v1_relat_1(k5_relat_1(X0,X1))
      | ~ v1_relat_1(X1)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1] :
      ( ( v1_relat_1(X1)
        & v1_relat_1(X0) )
     => v1_relat_1(k5_relat_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t33_funct_2.p',dt_k5_relat_1)).

fof(f311,plain,
    ( spl6_64
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f161,f145,f309])).

fof(f161,plain,
    ( k1_relset_1(sK1,sK2,sK4) = k1_relat_1(sK4)
    | ~ spl6_16 ),
    inference(resolution,[],[f146,f99])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f58])).

fof(f58,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t33_funct_2.p',redefinition_k1_relset_1)).

fof(f307,plain,
    ( spl6_62
    | ~ spl6_58 ),
    inference(avatar_split_clause,[],[f302,f295,f305])).

fof(f295,plain,
    ( spl6_58
  <=> m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_58])])).

fof(f302,plain,
    ( r1_tarski(k1_relat_1(sK4),sK1)
    | ~ spl6_58 ),
    inference(resolution,[],[f296,f104])).

fof(f104,plain,(
    ! [X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(X1))
      | r1_tarski(X0,X1) ) ),
    inference(cnf_transformation,[],[f64])).

fof(f64,plain,(
    ! [X0,X1] :
      ( r1_tarski(X0,X1)
      | ~ m1_subset_1(X0,k1_zfmisc_1(X1)) ) ),
    inference(ennf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
     => r1_tarski(X0,X1) ) ),
    inference(unused_predicate_definition_removal,[],[f23])).

fof(f23,axiom,(
    ! [X0,X1] :
      ( m1_subset_1(X0,k1_zfmisc_1(X1))
    <=> r1_tarski(X0,X1) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t33_funct_2.p',t3_subset)).

fof(f296,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK1))
    | ~ spl6_58 ),
    inference(avatar_component_clause,[],[f295])).

fof(f297,plain,
    ( spl6_58
    | ~ spl6_16
    | ~ spl6_54 ),
    inference(avatar_split_clause,[],[f289,f286,f145,f295])).

fof(f286,plain,
    ( spl6_54
  <=> m1_subset_1(k1_relset_1(sK1,sK2,sK4),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_54])])).

fof(f289,plain,
    ( m1_subset_1(k1_relat_1(sK4),k1_zfmisc_1(sK1))
    | ~ spl6_16
    | ~ spl6_54 ),
    inference(forward_demodulation,[],[f287,f161])).

fof(f287,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK2,sK4),k1_zfmisc_1(sK1))
    | ~ spl6_54 ),
    inference(avatar_component_clause,[],[f286])).

fof(f288,plain,
    ( spl6_54
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f160,f145,f286])).

fof(f160,plain,
    ( m1_subset_1(k1_relset_1(sK1,sK2,sK4),k1_zfmisc_1(sK1))
    | ~ spl6_16 ),
    inference(resolution,[],[f146,f98])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f57])).

fof(f57,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k1_relset_1(X0,X1,X2),k1_zfmisc_1(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t33_funct_2.p',dt_k1_relset_1)).

fof(f261,plain,
    ( spl6_48
    | ~ spl6_46 ),
    inference(avatar_split_clause,[],[f256,f253,f259])).

fof(f253,plain,
    ( spl6_46
  <=> m1_subset_1(sK1,k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f256,plain,
    ( r1_tarski(sK1,sK1)
    | ~ spl6_46 ),
    inference(resolution,[],[f254,f104])).

fof(f254,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl6_46 ),
    inference(avatar_component_clause,[],[f253])).

fof(f255,plain,
    ( spl6_46
    | ~ spl6_34
    | ~ spl6_44 ),
    inference(avatar_split_clause,[],[f251,f248,f225,f253])).

fof(f248,plain,
    ( spl6_44
  <=> m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_44])])).

fof(f251,plain,
    ( m1_subset_1(sK1,k1_zfmisc_1(sK1))
    | ~ spl6_34
    | ~ spl6_44 ),
    inference(forward_demodulation,[],[f249,f226])).

fof(f249,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl6_44 ),
    inference(avatar_component_clause,[],[f248])).

fof(f250,plain,
    ( spl6_44
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f187,f149,f248])).

fof(f187,plain,
    ( m1_subset_1(k2_relat_1(sK3),k1_zfmisc_1(sK1))
    | ~ spl6_18 ),
    inference(forward_demodulation,[],[f180,f175])).

fof(f175,plain,
    ( k2_relat_1(sK3) = k2_relset_1(sK0,sK1,sK3)
    | ~ spl6_18 ),
    inference(resolution,[],[f150,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k2_relat_1(X2) = k2_relset_1(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relat_1(X2) = k2_relset_1(X0,X1,X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t33_funct_2.p',redefinition_k2_relset_1)).

fof(f180,plain,
    ( m1_subset_1(k2_relset_1(sK0,sK1,sK3),k1_zfmisc_1(sK1))
    | ~ spl6_18 ),
    inference(resolution,[],[f150,f105])).

fof(f105,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    inference(cnf_transformation,[],[f65])).

fof(f65,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k2_relset_1(X0,X1,X2),k1_zfmisc_1(X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t33_funct_2.p',dt_k2_relset_1)).

fof(f227,plain,
    ( spl6_34
    | ~ spl6_8
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(avatar_split_clause,[],[f215,f207,f197,f129,f225])).

fof(f129,plain,
    ( spl6_8
  <=> v2_funct_2(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f207,plain,
    ( spl6_28
  <=> v5_relat_1(sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f215,plain,
    ( k2_relat_1(sK3) = sK1
    | ~ spl6_8
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f214,f130])).

fof(f130,plain,
    ( v2_funct_2(sK3,sK1)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f129])).

fof(f214,plain,
    ( k2_relat_1(sK3) = sK1
    | ~ v2_funct_2(sK3,sK1)
    | ~ spl6_24
    | ~ spl6_28 ),
    inference(subsumption_resolution,[],[f213,f198])).

fof(f213,plain,
    ( ~ v1_relat_1(sK3)
    | k2_relat_1(sK3) = sK1
    | ~ v2_funct_2(sK3,sK1)
    | ~ spl6_28 ),
    inference(resolution,[],[f208,f81])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v5_relat_1(X1,X0)
      | ~ v1_relat_1(X1)
      | k2_relat_1(X1) = X0
      | ~ v2_funct_2(X1,X0) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f208,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ spl6_28 ),
    inference(avatar_component_clause,[],[f207])).

fof(f219,plain,
    ( spl6_30
    | ~ spl6_10
    | ~ spl6_20
    | ~ spl6_26 ),
    inference(avatar_split_clause,[],[f212,f203,f189,f133,f217])).

fof(f133,plain,
    ( spl6_10
  <=> v2_funct_2(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f203,plain,
    ( spl6_26
  <=> v5_relat_1(sK4,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f212,plain,
    ( k2_relat_1(sK4) = sK2
    | ~ spl6_10
    | ~ spl6_20
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f211,f134])).

fof(f134,plain,
    ( v2_funct_2(sK4,sK2)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f133])).

fof(f211,plain,
    ( k2_relat_1(sK4) = sK2
    | ~ v2_funct_2(sK4,sK2)
    | ~ spl6_20
    | ~ spl6_26 ),
    inference(subsumption_resolution,[],[f210,f190])).

fof(f210,plain,
    ( ~ v1_relat_1(sK4)
    | k2_relat_1(sK4) = sK2
    | ~ v2_funct_2(sK4,sK2)
    | ~ spl6_26 ),
    inference(resolution,[],[f204,f81])).

fof(f204,plain,
    ( v5_relat_1(sK4,sK2)
    | ~ spl6_26 ),
    inference(avatar_component_clause,[],[f203])).

fof(f209,plain,
    ( spl6_28
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f176,f149,f207])).

fof(f176,plain,
    ( v5_relat_1(sK3,sK1)
    | ~ spl6_18 ),
    inference(resolution,[],[f150,f96])).

fof(f205,plain,
    ( spl6_26
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f158,f145,f203])).

fof(f158,plain,
    ( v5_relat_1(sK4,sK2)
    | ~ spl6_16 ),
    inference(resolution,[],[f146,f96])).

fof(f199,plain,
    ( spl6_24
    | ~ spl6_18 ),
    inference(avatar_split_clause,[],[f177,f149,f197])).

fof(f177,plain,
    ( v1_relat_1(sK3)
    | ~ spl6_18 ),
    inference(resolution,[],[f150,f97])).

fof(f97,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f30])).

fof(f30,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t33_funct_2.p',cc1_relset_1)).

fof(f195,plain,(
    ~ spl6_23 ),
    inference(avatar_split_clause,[],[f71,f193])).

fof(f71,plain,(
    ~ v2_funct_2(k1_partfun1(sK0,sK1,sK1,sK2,sK3,sK4),sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2)
                  & v2_funct_2(X4,X2)
                  & v2_funct_2(X3,X1)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_2(X4,X1,X2)
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ? [X0,X1] :
      ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ~ v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2)
                  & v2_funct_2(X4,X2)
                  & v2_funct_2(X3,X1)
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                  & v1_funct_2(X4,X1,X2)
                  & v1_funct_1(X4) )
              & m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
              & v1_funct_2(X3,X0,X1)
              & v1_funct_1(X3) )
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,negated_conjecture,(
    ~ ! [X0,X1] :
        ( ~ v1_xboole_0(X1)
       => ! [X2] :
            ( ~ v1_xboole_0(X2)
           => ! [X3] :
                ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                  & v1_funct_2(X3,X0,X1)
                  & v1_funct_1(X3) )
               => ! [X4] :
                    ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                      & v1_funct_2(X4,X1,X2)
                      & v1_funct_1(X4) )
                   => ( ( v2_funct_2(X4,X2)
                        & v2_funct_2(X3,X1) )
                     => v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f1])).

fof(f1,conjecture,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( ~ v1_xboole_0(X2)
         => ! [X3] :
              ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
                & v1_funct_2(X3,X0,X1)
                & v1_funct_1(X3) )
             => ! [X4] :
                  ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
                    & v1_funct_2(X4,X1,X2)
                    & v1_funct_1(X4) )
                 => ( ( v2_funct_2(X4,X2)
                      & v2_funct_2(X3,X1) )
                   => v2_funct_2(k1_partfun1(X0,X1,X1,X2,X3,X4),X2) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/funct_2__t33_funct_2.p',t33_funct_2)).

fof(f191,plain,
    ( spl6_20
    | ~ spl6_16 ),
    inference(avatar_split_clause,[],[f159,f145,f189])).

fof(f159,plain,
    ( v1_relat_1(sK4)
    | ~ spl6_16 ),
    inference(resolution,[],[f146,f97])).

fof(f151,plain,(
    spl6_18 ),
    inference(avatar_split_clause,[],[f74,f149])).

fof(f74,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f36])).

fof(f147,plain,(
    spl6_16 ),
    inference(avatar_split_clause,[],[f68,f145])).

fof(f68,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK1,sK2))) ),
    inference(cnf_transformation,[],[f36])).

fof(f139,plain,(
    spl6_12 ),
    inference(avatar_split_clause,[],[f67,f137])).

fof(f67,plain,(
    v1_funct_2(sK4,sK1,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f135,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f70,f133])).

fof(f70,plain,(
    v2_funct_2(sK4,sK2) ),
    inference(cnf_transformation,[],[f36])).

fof(f131,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f69,f129])).

fof(f69,plain,(
    v2_funct_2(sK3,sK1) ),
    inference(cnf_transformation,[],[f36])).

fof(f119,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f72,f117])).

fof(f72,plain,(
    v1_funct_1(sK3) ),
    inference(cnf_transformation,[],[f36])).

fof(f115,plain,(
    spl6_0 ),
    inference(avatar_split_clause,[],[f66,f113])).

fof(f66,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f36])).
%------------------------------------------------------------------------------
