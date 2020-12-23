%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:17:26 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  229 ( 613 expanded)
%              Number of leaves         :   53 ( 290 expanded)
%              Depth                    :   19
%              Number of atoms          : 1298 (5079 expanded)
%              Number of equality atoms :  217 (1034 expanded)
%              Maximal formula depth    :   25 (   7 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f462,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f105,f109,f113,f117,f121,f125,f129,f133,f137,f141,f145,f149,f153,f157,f175,f182,f203,f224,f227,f232,f236,f246,f249,f254,f258,f276,f289,f298,f311,f316,f428,f438,f443,f455,f461])).

fof(f461,plain,
    ( spl6_3
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_35
    | ~ spl6_55 ),
    inference(avatar_split_clause,[],[f459,f453,f286,f127,f123,f119,f127,f119,f103])).

fof(f103,plain,
    ( spl6_3
  <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f119,plain,
    ( spl6_7
  <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f123,plain,
    ( spl6_8
  <=> v1_funct_2(sK4,sK2,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f127,plain,
    ( spl6_9
  <=> v1_funct_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f286,plain,
    ( spl6_35
  <=> k1_xboole_0 = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f453,plain,
    ( spl6_55
  <=> ! [X1] :
        ( k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f459,plain,
    ( ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_35
    | ~ spl6_55 ),
    inference(trivial_inequality_removal,[],[f458])).

fof(f458,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_35
    | ~ spl6_55 ),
    inference(forward_demodulation,[],[f457,f287])).

fof(f287,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f286])).

fof(f457,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | ~ spl6_55 ),
    inference(forward_demodulation,[],[f456,f208])).

fof(f208,plain,
    ( ! [X0] : k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(resolution,[],[f195,f120])).

fof(f120,plain,
    ( m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f119])).

fof(f195,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | k2_partfun1(X3,X4,sK4,X5) = k7_relat_1(sK4,X5) )
    | ~ spl6_9 ),
    inference(resolution,[],[f83,f128])).

fof(f128,plain,
    ( v1_funct_1(sK4)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f127])).

fof(f83,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2,X3] :
      ( k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).

fof(f456,plain,
    ( ~ v1_funct_1(sK4)
    | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | ~ spl6_8
    | ~ spl6_55 ),
    inference(resolution,[],[f454,f124])).

fof(f124,plain,
    ( v1_funct_2(sK4,sK2,sK1)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f123])).

fof(f454,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) )
    | ~ spl6_55 ),
    inference(avatar_component_clause,[],[f453])).

fof(f455,plain,
    ( spl6_14
    | spl6_55
    | ~ spl6_13
    | ~ spl6_33
    | ~ spl6_35
    | ~ spl6_53 ),
    inference(avatar_split_clause,[],[f451,f441,f286,f274,f143,f453,f147])).

fof(f147,plain,
    ( spl6_14
  <=> v1_xboole_0(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f143,plain,
    ( spl6_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f274,plain,
    ( spl6_33
  <=> k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f441,plain,
    ( spl6_53
  <=> ! [X1,X0] :
        ( v1_xboole_0(X0)
        | sK5 = k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ v1_funct_1(X1)
        | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0,sK3))
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f451,plain,
    ( ! [X1] :
        ( k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
        | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_xboole_0(sK2) )
    | ~ spl6_13
    | ~ spl6_33
    | ~ spl6_35
    | ~ spl6_53 ),
    inference(forward_demodulation,[],[f450,f287])).

fof(f450,plain,
    ( ! [X1] :
        ( k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
        | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | v1_xboole_0(sK2) )
    | ~ spl6_13
    | ~ spl6_33
    | ~ spl6_53 ),
    inference(forward_demodulation,[],[f445,f275])).

fof(f275,plain,
    ( k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f274])).

fof(f445,plain,
    ( ! [X1] :
        ( sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        | ~ v1_funct_2(X1,sK2,sK1)
        | ~ v1_funct_1(X1)
        | k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3))
        | v1_xboole_0(sK2) )
    | ~ spl6_13
    | ~ spl6_53 ),
    inference(resolution,[],[f442,f144])).

fof(f144,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | ~ spl6_13 ),
    inference(avatar_component_clause,[],[f143])).

fof(f442,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | sK5 = k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ v1_funct_1(X1)
        | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0,sK3))
        | v1_xboole_0(X0) )
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f441])).

fof(f443,plain,
    ( spl6_53
    | spl6_16
    | ~ spl6_11
    | ~ spl6_52 ),
    inference(avatar_split_clause,[],[f439,f436,f135,f155,f441])).

fof(f155,plain,
    ( spl6_16
  <=> v1_xboole_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).

fof(f135,plain,
    ( spl6_11
  <=> m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f436,plain,
    ( spl6_52
  <=> ! [X1,X0,X2] :
        ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
        | v1_xboole_0(X2)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X2))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | sK5 = k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).

fof(f439,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(sK0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(sK0))
        | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0,sK3))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | sK5 = k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3) )
    | ~ spl6_11
    | ~ spl6_52 ),
    inference(resolution,[],[f437,f136])).

fof(f136,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f135])).

fof(f437,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK3,k1_zfmisc_1(X2))
        | v1_xboole_0(X2)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
        | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | sK5 = k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) )
    | ~ spl6_52 ),
    inference(avatar_component_clause,[],[f436])).

fof(f438,plain,
    ( spl6_15
    | spl6_12
    | ~ spl6_5
    | spl6_52
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f434,f115,f107,f436,f111,f139,f151])).

fof(f151,plain,
    ( spl6_15
  <=> v1_xboole_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f139,plain,
    ( spl6_12
  <=> v1_xboole_0(sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

fof(f111,plain,
    ( spl6_5
  <=> v1_funct_2(sK5,sK3,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f107,plain,
    ( spl6_4
  <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f115,plain,
    ( spl6_6
  <=> v1_funct_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f434,plain,
    ( ! [X2,X0,X1] :
        ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3))
        | ~ v1_funct_2(sK5,sK3,sK1)
        | sK5 = k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X2))
        | v1_xboole_0(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
        | v1_xboole_0(X0)
        | v1_xboole_0(sK1)
        | v1_xboole_0(X2) )
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f433,f197])).

fof(f197,plain,
    ( ! [X0] : k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(resolution,[],[f194,f108])).

fof(f108,plain,
    ( m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ spl6_4 ),
    inference(avatar_component_clause,[],[f107])).

fof(f194,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2) )
    | ~ spl6_6 ),
    inference(resolution,[],[f83,f116])).

fof(f116,plain,
    ( v1_funct_1(sK5)
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f115])).

fof(f433,plain,
    ( ! [X2,X0,X1] :
        ( k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X2,X0,sK3))
        | ~ v1_funct_2(sK5,sK3,sK1)
        | sK5 = k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3)
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1)))
        | ~ v1_funct_2(X1,X0,sK1)
        | ~ v1_funct_1(X1)
        | ~ m1_subset_1(sK3,k1_zfmisc_1(X2))
        | v1_xboole_0(sK3)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X2))
        | v1_xboole_0(X0)
        | v1_xboole_0(sK1)
        | v1_xboole_0(X2) )
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(resolution,[],[f430,f108])).

fof(f430,plain,
    ( ! [X4,X2,X0,X3,X1] :
        ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X4,X1)))
        | k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,sK5,k9_subset_1(X3,X0,X4))
        | ~ v1_funct_2(sK5,X4,X1)
        | sK5 = k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,sK5),X4)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X4,k1_zfmisc_1(X3))
        | v1_xboole_0(X4)
        | ~ m1_subset_1(X0,k1_zfmisc_1(X3))
        | v1_xboole_0(X0)
        | v1_xboole_0(X1)
        | v1_xboole_0(X3) )
    | ~ spl6_6 ),
    inference(resolution,[],[f163,f116])).

fof(f163,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ v1_funct_1(X5)
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f161,f84])).

fof(f84,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) )
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
        & v1_funct_2(X5,X3,X1)
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
        & v1_funct_2(X4,X2,X1)
        & v1_funct_1(X4)
        & m1_subset_1(X3,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X3)
        & m1_subset_1(X2,k1_zfmisc_1(X0))
        & ~ v1_xboole_0(X2)
        & ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
        & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
        & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).

fof(f161,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f159,f85])).

fof(f85,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f159,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f93,f86])).

fof(f86,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f93,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
      | ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(equality_resolution,[],[f66])).

fof(f66,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
      | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(X6)
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                  | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5
                                  | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4 )
                                & ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                    & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 )
                                  | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                  | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5
                                  | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4 )
                                & ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                    & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 )
                                  | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                  & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( ! [X4] :
                      ( ! [X5] :
                          ( ! [X6] :
                              ( ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                              <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                  & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) )
                              | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                              | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                              | ~ v1_funct_1(X6) )
                          | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                          | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          | ~ v1_funct_2(X5,X3,X1)
                          | ~ v1_funct_1(X5) )
                      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      | ~ v1_funct_2(X4,X2,X1)
                      | ~ v1_funct_1(X4) )
                  | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
                  | v1_xboole_0(X3) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
              | v1_xboole_0(X2) )
          | v1_xboole_0(X1) )
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ! [X4] :
                      ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                        & v1_funct_2(X4,X2,X1)
                        & v1_funct_1(X4) )
                     => ! [X5] :
                          ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                            & v1_funct_2(X5,X3,X1)
                            & v1_funct_1(X5) )
                         => ( k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
                           => ! [X6] :
                                ( ( m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
                                  & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
                                  & v1_funct_1(X6) )
                               => ( k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6
                                <=> ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5
                                    & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 ) ) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).

fof(f428,plain,
    ( spl6_16
    | spl6_15
    | spl6_14
    | ~ spl6_13
    | spl6_12
    | ~ spl6_11
    | ~ spl6_9
    | ~ spl6_8
    | ~ spl6_7
    | ~ spl6_6
    | ~ spl6_5
    | ~ spl6_4
    | spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_33
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f423,f286,f274,f127,f119,f115,f107,f100,f107,f111,f115,f119,f123,f127,f135,f139,f143,f147,f151,f155])).

fof(f100,plain,
    ( spl6_2
  <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f423,plain,
    ( ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_33
    | ~ spl6_35 ),
    inference(trivial_inequality_removal,[],[f422])).

fof(f422,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_33
    | ~ spl6_35 ),
    inference(forward_demodulation,[],[f421,f287])).

fof(f421,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_33
    | ~ spl6_35 ),
    inference(forward_demodulation,[],[f420,f208])).

fof(f420,plain,
    ( k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_33
    | ~ spl6_35 ),
    inference(forward_demodulation,[],[f419,f287])).

fof(f419,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_33 ),
    inference(forward_demodulation,[],[f418,f275])).

fof(f418,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_2
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f417,f197])).

fof(f417,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_2 ),
    inference(trivial_inequality_removal,[],[f416])).

fof(f416,plain,
    ( sK4 != sK4
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    | ~ v1_funct_2(sK5,sK3,sK1)
    | ~ v1_funct_1(sK5)
    | ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    | ~ v1_funct_2(sK4,sK2,sK1)
    | ~ v1_funct_1(sK4)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK3)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(sK0))
    | v1_xboole_0(sK2)
    | v1_xboole_0(sK1)
    | v1_xboole_0(sK0)
    | spl6_2 ),
    inference(superposition,[],[f101,f162])).

fof(f162,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f160,f84])).

fof(f160,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f158,f85])).

fof(f158,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(subsumption_resolution,[],[f94,f86])).

fof(f94,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
      | ~ m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(equality_resolution,[],[f65])).

fof(f65,plain,(
    ! [X6,X4,X2,X0,X5,X3,X1] :
      ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4
      | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6
      | ~ m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1)))
      | ~ v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1)
      | ~ v1_funct_1(X6)
      | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
      | ~ v1_funct_2(X5,X3,X1)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
      | ~ v1_funct_2(X4,X2,X1)
      | ~ v1_funct_1(X4)
      | ~ m1_subset_1(X3,k1_zfmisc_1(X0))
      | v1_xboole_0(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0))
      | v1_xboole_0(X2)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f101,plain,
    ( sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | spl6_2 ),
    inference(avatar_component_clause,[],[f100])).

fof(f316,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f311,plain,
    ( ~ spl6_11
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_18
    | spl6_20
    | ~ spl6_25
    | ~ spl6_31 ),
    inference(avatar_split_clause,[],[f310,f264,f222,f201,f180,f127,f119,f135])).

fof(f180,plain,
    ( spl6_18
  <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).

fof(f201,plain,
    ( spl6_20
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).

fof(f222,plain,
    ( spl6_25
  <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).

fof(f264,plain,
    ( spl6_31
  <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f310,plain,
    ( ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_18
    | spl6_20
    | ~ spl6_25
    | ~ spl6_31 ),
    inference(trivial_inequality_removal,[],[f309])).

% (25074)Refutation not found, incomplete strategy% (25074)------------------------------
% (25074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25074)Termination reason: Refutation not found, incomplete strategy

% (25074)Memory used [KB]: 11513
% (25074)Time elapsed: 0.124 s
% (25074)------------------------------
% (25074)------------------------------
% (25073)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% (25061)Refutation not found, incomplete strategy% (25061)------------------------------
% (25061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (25061)Termination reason: Refutation not found, incomplete strategy

% (25061)Memory used [KB]: 11385
% (25061)Time elapsed: 0.192 s
% (25061)------------------------------
% (25061)------------------------------
fof(f309,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_18
    | spl6_20
    | ~ spl6_25
    | ~ spl6_31 ),
    inference(forward_demodulation,[],[f308,f266])).

fof(f266,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)
    | ~ spl6_25 ),
    inference(avatar_component_clause,[],[f222])).

fof(f308,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_7
    | ~ spl6_9
    | ~ spl6_18
    | spl6_20
    | ~ spl6_31 ),
    inference(forward_demodulation,[],[f307,f208])).

fof(f307,plain,
    ( k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_18
    | spl6_20
    | ~ spl6_31 ),
    inference(forward_demodulation,[],[f306,f265])).

fof(f265,plain,
    ( k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)
    | ~ spl6_31 ),
    inference(avatar_component_clause,[],[f264])).

fof(f306,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0)
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_18
    | spl6_20 ),
    inference(forward_demodulation,[],[f304,f181])).

fof(f181,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl6_18 ),
    inference(avatar_component_clause,[],[f180])).

fof(f304,plain,
    ( k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3)))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | spl6_20 ),
    inference(superposition,[],[f202,f90])).

fof(f90,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(definition_unfolding,[],[f80,f71])).

fof(f71,plain,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).

fof(f80,plain,(
    ! [X2,X0,X1] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(X0)) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(X0))
     => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).

fof(f202,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_20 ),
    inference(avatar_component_clause,[],[f201])).

fof(f298,plain,
    ( ~ spl6_11
    | ~ spl6_24
    | ~ spl6_18
    | spl6_34 ),
    inference(avatar_split_clause,[],[f297,f283,f180,f219,f135])).

fof(f219,plain,
    ( spl6_24
  <=> r1_xboole_0(k1_xboole_0,k1_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).

fof(f283,plain,
    ( spl6_34
  <=> r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f297,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK5))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | ~ spl6_18
    | spl6_34 ),
    inference(forward_demodulation,[],[f291,f181])).

fof(f291,plain,
    ( ~ r1_xboole_0(k1_setfam_1(k2_tarski(sK2,sK3)),k1_relat_1(sK5))
    | ~ m1_subset_1(sK3,k1_zfmisc_1(sK0))
    | spl6_34 ),
    inference(superposition,[],[f284,f90])).

fof(f284,plain,
    ( ~ r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5))
    | spl6_34 ),
    inference(avatar_component_clause,[],[f283])).

fof(f289,plain,
    ( ~ spl6_23
    | ~ spl6_34
    | spl6_35
    | ~ spl6_33 ),
    inference(avatar_split_clause,[],[f279,f274,f286,f283,f216])).

fof(f216,plain,
    ( spl6_23
  <=> v1_relat_1(sK5) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).

fof(f279,plain,
    ( k1_xboole_0 = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | ~ spl6_33 ),
    inference(superposition,[],[f68,f275])).

fof(f68,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = k7_relat_1(X0,X1)
      | ~ r1_xboole_0(X1,k1_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k1_xboole_0 = k7_relat_1(X0,X1)
          | ~ r1_xboole_0(X1,k1_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( r1_xboole_0(X1,k1_relat_1(X0))
         => k1_xboole_0 = k7_relat_1(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).

fof(f276,plain,
    ( spl6_33
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(avatar_split_clause,[],[f272,f127,f119,f115,f107,f97,f274])).

fof(f97,plain,
    ( spl6_1
  <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f272,plain,
    ( k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_9 ),
    inference(forward_demodulation,[],[f271,f208])).

fof(f271,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ spl6_1
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(forward_demodulation,[],[f259,f197])).

fof(f259,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f258,plain,(
    spl6_29 ),
    inference(avatar_contradiction_clause,[],[f257])).

fof(f257,plain,
    ( $false
    | spl6_29 ),
    inference(trivial_inequality_removal,[],[f256])).

fof(f256,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl6_29 ),
    inference(superposition,[],[f253,f164])).

fof(f164,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0)) ),
    inference(superposition,[],[f87,f70])).

fof(f70,plain,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

fof(f87,plain,(
    ! [X0] : k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0)) ),
    inference(definition_unfolding,[],[f64,f71])).

fof(f64,plain,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

fof(f253,plain,
    ( k1_xboole_0 != k1_setfam_1(k2_tarski(k1_xboole_0,k1_relat_1(sK4)))
    | spl6_29 ),
    inference(avatar_component_clause,[],[f252])).

fof(f252,plain,
    ( spl6_29
  <=> k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,k1_relat_1(sK4))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f254,plain,
    ( ~ spl6_29
    | spl6_28 ),
    inference(avatar_split_clause,[],[f250,f244,f252])).

fof(f244,plain,
    ( spl6_28
  <=> r1_xboole_0(k1_xboole_0,k1_relat_1(sK4)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).

fof(f250,plain,
    ( k1_xboole_0 != k1_setfam_1(k2_tarski(k1_xboole_0,k1_relat_1(sK4)))
    | spl6_28 ),
    inference(resolution,[],[f245,f88])).

fof(f88,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f79,f71])).

fof(f79,plain,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
      | k3_xboole_0(X0,X1) != k1_xboole_0 ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1] :
      ( ( r1_xboole_0(X0,X1)
        | k3_xboole_0(X0,X1) != k1_xboole_0 )
      & ( k3_xboole_0(X0,X1) = k1_xboole_0
        | ~ r1_xboole_0(X0,X1) ) ) ),
    inference(nnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( r1_xboole_0(X0,X1)
    <=> k3_xboole_0(X0,X1) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

fof(f245,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK4))
    | spl6_28 ),
    inference(avatar_component_clause,[],[f244])).

fof(f249,plain,
    ( ~ spl6_7
    | spl6_27 ),
    inference(avatar_contradiction_clause,[],[f248])).

fof(f248,plain,
    ( $false
    | ~ spl6_7
    | spl6_27 ),
    inference(subsumption_resolution,[],[f120,f247])).

fof(f247,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_27 ),
    inference(resolution,[],[f242,f81])).

fof(f81,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f242,plain,
    ( ~ v1_relat_1(sK4)
    | spl6_27 ),
    inference(avatar_component_clause,[],[f241])).

fof(f241,plain,
    ( spl6_27
  <=> v1_relat_1(sK4) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).

fof(f246,plain,
    ( ~ spl6_27
    | ~ spl6_28
    | spl6_25 ),
    inference(avatar_split_clause,[],[f239,f222,f244,f241])).

fof(f239,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl6_25 ),
    inference(trivial_inequality_removal,[],[f238])).

fof(f238,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK4))
    | ~ v1_relat_1(sK4)
    | spl6_25 ),
    inference(superposition,[],[f223,f68])).

fof(f223,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | spl6_25 ),
    inference(avatar_component_clause,[],[f222])).

fof(f236,plain,(
    spl6_26 ),
    inference(avatar_contradiction_clause,[],[f235])).

fof(f235,plain,
    ( $false
    | spl6_26 ),
    inference(trivial_inequality_removal,[],[f234])).

fof(f234,plain,
    ( k1_xboole_0 != k1_xboole_0
    | spl6_26 ),
    inference(superposition,[],[f231,f164])).

fof(f231,plain,
    ( k1_xboole_0 != k1_setfam_1(k2_tarski(k1_xboole_0,k1_relat_1(sK5)))
    | spl6_26 ),
    inference(avatar_component_clause,[],[f230])).

fof(f230,plain,
    ( spl6_26
  <=> k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,k1_relat_1(sK5))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).

fof(f232,plain,
    ( ~ spl6_26
    | spl6_24 ),
    inference(avatar_split_clause,[],[f228,f219,f230])).

fof(f228,plain,
    ( k1_xboole_0 != k1_setfam_1(k2_tarski(k1_xboole_0,k1_relat_1(sK5)))
    | spl6_24 ),
    inference(resolution,[],[f220,f88])).

fof(f220,plain,
    ( ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK5))
    | spl6_24 ),
    inference(avatar_component_clause,[],[f219])).

fof(f227,plain,
    ( ~ spl6_4
    | spl6_23 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | ~ spl6_4
    | spl6_23 ),
    inference(subsumption_resolution,[],[f108,f225])).

fof(f225,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl6_23 ),
    inference(resolution,[],[f217,f81])).

fof(f217,plain,
    ( ~ v1_relat_1(sK5)
    | spl6_23 ),
    inference(avatar_component_clause,[],[f216])).

fof(f224,plain,
    ( ~ spl6_23
    | ~ spl6_24
    | ~ spl6_25
    | spl6_22 ),
    inference(avatar_split_clause,[],[f214,f211,f222,f219,f216])).

fof(f211,plain,
    ( spl6_22
  <=> k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(sK4,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).

fof(f214,plain,
    ( k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0)
    | ~ r1_xboole_0(k1_xboole_0,k1_relat_1(sK5))
    | ~ v1_relat_1(sK5)
    | spl6_22 ),
    inference(superposition,[],[f212,f68])).

fof(f212,plain,
    ( k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0)
    | spl6_22 ),
    inference(avatar_component_clause,[],[f211])).

fof(f203,plain,
    ( ~ spl6_20
    | spl6_1
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(avatar_split_clause,[],[f198,f115,f107,f97,f201])).

fof(f198,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_1
    | ~ spl6_4
    | ~ spl6_6 ),
    inference(superposition,[],[f98,f197])).

fof(f98,plain,
    ( k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))
    | spl6_1 ),
    inference(avatar_component_clause,[],[f97])).

fof(f182,plain,
    ( spl6_18
    | ~ spl6_17 ),
    inference(avatar_split_clause,[],[f178,f173,f180])).

fof(f173,plain,
    ( spl6_17
  <=> r1_xboole_0(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).

fof(f178,plain,
    ( k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))
    | ~ spl6_17 ),
    inference(resolution,[],[f174,f89])).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ r1_xboole_0(X0,X1)
      | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1)) ) ),
    inference(definition_unfolding,[],[f78,f71])).

fof(f78,plain,(
    ! [X0,X1] :
      ( k3_xboole_0(X0,X1) = k1_xboole_0
      | ~ r1_xboole_0(X0,X1) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f174,plain,
    ( r1_xboole_0(sK2,sK3)
    | ~ spl6_17 ),
    inference(avatar_component_clause,[],[f173])).

fof(f175,plain,
    ( spl6_14
    | spl6_12
    | spl6_17
    | ~ spl6_10 ),
    inference(avatar_split_clause,[],[f169,f131,f173,f139,f147])).

fof(f131,plain,
    ( spl6_10
  <=> r1_subset_1(sK2,sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f169,plain,
    ( r1_xboole_0(sK2,sK3)
    | v1_xboole_0(sK3)
    | v1_xboole_0(sK2)
    | ~ spl6_10 ),
    inference(resolution,[],[f74,f132])).

fof(f132,plain,
    ( r1_subset_1(sK2,sK3)
    | ~ spl6_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f74,plain,(
    ! [X0,X1] :
      ( ~ r1_subset_1(X0,X1)
      | r1_xboole_0(X0,X1)
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1] :
      ( ( ( r1_subset_1(X0,X1)
          | ~ r1_xboole_0(X0,X1) )
        & ( r1_xboole_0(X0,X1)
          | ~ r1_subset_1(X0,X1) ) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(nnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1] :
      ( ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) )
      | v1_xboole_0(X1)
      | v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1] :
      ( ( ~ v1_xboole_0(X1)
        & ~ v1_xboole_0(X0) )
     => ( r1_subset_1(X0,X1)
      <=> r1_xboole_0(X0,X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).

fof(f157,plain,(
    ~ spl6_16 ),
    inference(avatar_split_clause,[],[f50,f155])).

fof(f50,plain,(
    ~ v1_xboole_0(sK0) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,
    ( ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
      | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
      | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) )
    & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
    & v1_funct_2(sK5,sK3,sK1)
    & v1_funct_1(sK5)
    & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
    & v1_funct_2(sK4,sK2,sK1)
    & v1_funct_1(sK4)
    & r1_subset_1(sK2,sK3)
    & m1_subset_1(sK3,k1_zfmisc_1(sK0))
    & ~ v1_xboole_0(sK3)
    & m1_subset_1(sK2,k1_zfmisc_1(sK0))
    & ~ v1_xboole_0(sK2)
    & ~ v1_xboole_0(sK1)
    & ~ v1_xboole_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f20,f43,f42,f41,f40,f39,f38])).

fof(f38,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ? [X3] :
                    ( ? [X4] :
                        ( ? [X5] :
                            ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                              | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                              | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                            & v1_funct_2(X5,X3,X1)
                            & v1_funct_1(X5) )
                        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                        & v1_funct_2(X4,X2,X1)
                        & v1_funct_1(X4) )
                    & r1_subset_1(X2,X3)
                    & m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                & m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
            & ~ v1_xboole_0(X1) )
        & ~ v1_xboole_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(sK0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(sK0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f39,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ? [X3] :
                ( ? [X4] :
                    ( ? [X5] :
                        ( ( k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5
                          | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4
                          | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3)) )
                        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                        & v1_funct_2(X5,X3,X1)
                        & v1_funct_1(X5) )
                    & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                    & v1_funct_2(X4,X2,X1)
                    & v1_funct_1(X4) )
                & r1_subset_1(X2,X3)
                & m1_subset_1(X3,k1_zfmisc_1(sK0))
                & ~ v1_xboole_0(X3) )
            & m1_subset_1(X2,k1_zfmisc_1(sK0))
            & ~ v1_xboole_0(X2) )
        & ~ v1_xboole_0(X1) )
   => ( ? [X2] :
          ( ? [X3] :
              ( ? [X4] :
                  ( ? [X5] :
                      ( ( k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5
                        | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4
                        | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3)) )
                      & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                      & v1_funct_2(X5,X3,sK1)
                      & v1_funct_1(X5) )
                  & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
                  & v1_funct_2(X4,X2,sK1)
                  & v1_funct_1(X4) )
              & r1_subset_1(X2,X3)
              & m1_subset_1(X3,k1_zfmisc_1(sK0))
              & ~ v1_xboole_0(X3) )
          & m1_subset_1(X2,k1_zfmisc_1(sK0))
          & ~ v1_xboole_0(X2) )
      & ~ v1_xboole_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f40,plain,
    ( ? [X2] :
        ( ? [X3] :
            ( ? [X4] :
                ( ? [X5] :
                    ( ( k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5
                      | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4
                      | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3)) )
                    & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                    & v1_funct_2(X5,X3,sK1)
                    & v1_funct_1(X5) )
                & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1)))
                & v1_funct_2(X4,X2,sK1)
                & v1_funct_1(X4) )
            & r1_subset_1(X2,X3)
            & m1_subset_1(X3,k1_zfmisc_1(sK0))
            & ~ v1_xboole_0(X3) )
        & m1_subset_1(X2,k1_zfmisc_1(sK0))
        & ~ v1_xboole_0(X2) )
   => ( ? [X3] :
          ( ? [X4] :
              ( ? [X5] :
                  ( ( k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5
                    | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4
                    | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3)) )
                  & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                  & v1_funct_2(X5,X3,sK1)
                  & v1_funct_1(X5) )
              & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
              & v1_funct_2(X4,sK2,sK1)
              & v1_funct_1(X4) )
          & r1_subset_1(sK2,X3)
          & m1_subset_1(X3,k1_zfmisc_1(sK0))
          & ~ v1_xboole_0(X3) )
      & m1_subset_1(sK2,k1_zfmisc_1(sK0))
      & ~ v1_xboole_0(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f41,plain,
    ( ? [X3] :
        ( ? [X4] :
            ( ? [X5] :
                ( ( k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5
                  | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4
                  | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3)) )
                & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1)))
                & v1_funct_2(X5,X3,sK1)
                & v1_funct_1(X5) )
            & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
            & v1_funct_2(X4,sK2,sK1)
            & v1_funct_1(X4) )
        & r1_subset_1(sK2,X3)
        & m1_subset_1(X3,k1_zfmisc_1(sK0))
        & ~ v1_xboole_0(X3) )
   => ( ? [X4] :
          ( ? [X5] :
              ( ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5
                | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4
                | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) )
              & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
              & v1_funct_2(X5,sK3,sK1)
              & v1_funct_1(X5) )
          & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
          & v1_funct_2(X4,sK2,sK1)
          & v1_funct_1(X4) )
      & r1_subset_1(sK2,sK3)
      & m1_subset_1(sK3,k1_zfmisc_1(sK0))
      & ~ v1_xboole_0(sK3) ) ),
    introduced(choice_axiom,[])).

fof(f42,plain,
    ( ? [X4] :
        ( ? [X5] :
            ( ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5
              | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4
              | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) )
            & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
            & v1_funct_2(X5,sK3,sK1)
            & v1_funct_1(X5) )
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
        & v1_funct_2(X4,sK2,sK1)
        & v1_funct_1(X4) )
   => ( ? [X5] :
          ( ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5
            | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2)
            | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) )
          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
          & v1_funct_2(X5,sK3,sK1)
          & v1_funct_1(X5) )
      & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))
      & v1_funct_2(sK4,sK2,sK1)
      & v1_funct_1(sK4) ) ),
    introduced(choice_axiom,[])).

fof(f43,plain,
    ( ? [X5] :
        ( ( k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5
          | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2)
          | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) )
        & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
        & v1_funct_2(X5,sK3,sK1)
        & v1_funct_1(X5) )
   => ( ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
        | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
        | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) )
      & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))
      & v1_funct_2(sK5,sK3,sK1)
      & v1_funct_1(sK5) ) ),
    introduced(choice_axiom,[])).

fof(f20,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ? [X3] :
                  ( ? [X4] :
                      ( ? [X5] :
                          ( ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5
                            | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4
                            | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) )
                          & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                          & v1_funct_2(X5,X3,X1)
                          & v1_funct_1(X5) )
                      & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                      & v1_funct_2(X4,X2,X1)
                      & v1_funct_1(X4) )
                  & r1_subset_1(X2,X3)
                  & m1_subset_1(X3,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X3) )
              & m1_subset_1(X2,k1_zfmisc_1(X0))
              & ~ v1_xboole_0(X2) )
          & ~ v1_xboole_0(X1) )
      & ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,negated_conjecture,(
    ~ ! [X0] :
        ( ~ v1_xboole_0(X0)
       => ! [X1] :
            ( ~ v1_xboole_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                  & ~ v1_xboole_0(X2) )
               => ! [X3] :
                    ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                      & ~ v1_xboole_0(X3) )
                   => ( r1_subset_1(X2,X3)
                     => ! [X4] :
                          ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                            & v1_funct_2(X4,X2,X1)
                            & v1_funct_1(X4) )
                         => ! [X5] :
                              ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                                & v1_funct_2(X5,X3,X1)
                                & v1_funct_1(X5) )
                             => ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
                                & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
                                & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) ) ) ) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f16])).

fof(f16,conjecture,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
     => ! [X1] :
          ( ~ v1_xboole_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(X0))
                & ~ v1_xboole_0(X2) )
             => ! [X3] :
                  ( ( m1_subset_1(X3,k1_zfmisc_1(X0))
                    & ~ v1_xboole_0(X3) )
                 => ( r1_subset_1(X2,X3)
                   => ! [X4] :
                        ( ( m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1)))
                          & v1_funct_2(X4,X2,X1)
                          & v1_funct_1(X4) )
                       => ! [X5] :
                            ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1)))
                              & v1_funct_2(X5,X3,X1)
                              & v1_funct_1(X5) )
                           => ( k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5
                              & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4
                              & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) ) ) ) ) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).

fof(f153,plain,(
    ~ spl6_15 ),
    inference(avatar_split_clause,[],[f51,f151])).

fof(f51,plain,(
    ~ v1_xboole_0(sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f149,plain,(
    ~ spl6_14 ),
    inference(avatar_split_clause,[],[f52,f147])).

fof(f52,plain,(
    ~ v1_xboole_0(sK2) ),
    inference(cnf_transformation,[],[f44])).

fof(f145,plain,(
    spl6_13 ),
    inference(avatar_split_clause,[],[f53,f143])).

fof(f53,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f141,plain,(
    ~ spl6_12 ),
    inference(avatar_split_clause,[],[f54,f139])).

fof(f54,plain,(
    ~ v1_xboole_0(sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f137,plain,(
    spl6_11 ),
    inference(avatar_split_clause,[],[f55,f135])).

fof(f55,plain,(
    m1_subset_1(sK3,k1_zfmisc_1(sK0)) ),
    inference(cnf_transformation,[],[f44])).

fof(f133,plain,(
    spl6_10 ),
    inference(avatar_split_clause,[],[f56,f131])).

fof(f56,plain,(
    r1_subset_1(sK2,sK3) ),
    inference(cnf_transformation,[],[f44])).

fof(f129,plain,(
    spl6_9 ),
    inference(avatar_split_clause,[],[f57,f127])).

fof(f57,plain,(
    v1_funct_1(sK4) ),
    inference(cnf_transformation,[],[f44])).

fof(f125,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f58,f123])).

fof(f58,plain,(
    v1_funct_2(sK4,sK2,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f121,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f59,f119])).

fof(f59,plain,(
    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f117,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f60,f115])).

fof(f60,plain,(
    v1_funct_1(sK5) ),
    inference(cnf_transformation,[],[f44])).

fof(f113,plain,(
    spl6_5 ),
    inference(avatar_split_clause,[],[f61,f111])).

fof(f61,plain,(
    v1_funct_2(sK5,sK3,sK1) ),
    inference(cnf_transformation,[],[f44])).

fof(f109,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f62,f107])).

fof(f62,plain,(
    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) ),
    inference(cnf_transformation,[],[f44])).

fof(f105,plain,
    ( ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3 ),
    inference(avatar_split_clause,[],[f63,f103,f100,f97])).

fof(f63,plain,
    ( sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)
    | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)
    | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) ),
    inference(cnf_transformation,[],[f44])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:15 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.52  % (25070)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.20/0.52  % (25053)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.20/0.53  % (25051)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.20/0.53  % (25066)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 0.20/0.54  % (25054)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 0.20/0.54  % (25055)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 0.20/0.54  % (25052)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.20/0.54  % (25059)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 0.20/0.54  % (25058)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 0.20/0.54  % (25083)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 0.20/0.54  % (25076)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 0.20/0.54  % (25065)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 0.20/0.54  % (25074)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 0.20/0.54  % (25080)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 0.20/0.55  % (25069)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 0.20/0.55  % (25081)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 0.20/0.55  % (25069)Refutation not found, incomplete strategy% (25069)------------------------------
% 0.20/0.55  % (25069)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.55  % (25069)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.55  
% 0.20/0.55  % (25069)Memory used [KB]: 10746
% 0.20/0.55  % (25069)Time elapsed: 0.136 s
% 0.20/0.55  % (25069)------------------------------
% 0.20/0.55  % (25069)------------------------------
% 0.20/0.55  % (25068)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 0.20/0.55  % (25075)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 0.20/0.55  % (25071)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_19 on theBenchmark
% 0.20/0.55  % (25061)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 0.20/0.55  % (25063)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.55  % (25057)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.20/0.55  % (25060)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 0.20/0.56  % (25067)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 0.20/0.56  % (25078)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 0.20/0.56  % (25062)lrs-3_4:1_afp=1000:afq=1.4:amm=sco:fde=none:gs=on:lcm=reverse:lma=on:nwc=1.5:stl=30:sd=1:ss=axioms:sp=reverse_arity:urr=on:updr=off:uhcvi=on_11 on theBenchmark
% 0.20/0.56  % (25072)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 0.20/0.57  % (25079)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 0.20/0.57  % (25056)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.20/0.58  % (25071)Refutation found. Thanks to Tanya!
% 0.20/0.58  % SZS status Theorem for theBenchmark
% 0.20/0.58  % SZS output start Proof for theBenchmark
% 0.20/0.58  fof(f462,plain,(
% 0.20/0.58    $false),
% 0.20/0.58    inference(avatar_sat_refutation,[],[f105,f109,f113,f117,f121,f125,f129,f133,f137,f141,f145,f149,f153,f157,f175,f182,f203,f224,f227,f232,f236,f246,f249,f254,f258,f276,f289,f298,f311,f316,f428,f438,f443,f455,f461])).
% 0.20/0.58  fof(f461,plain,(
% 0.20/0.58    spl6_3 | ~spl6_7 | ~spl6_9 | ~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_35 | ~spl6_55),
% 0.20/0.58    inference(avatar_split_clause,[],[f459,f453,f286,f127,f123,f119,f127,f119,f103])).
% 0.20/0.58  fof(f103,plain,(
% 0.20/0.58    spl6_3 <=> sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.20/0.58  fof(f119,plain,(
% 0.20/0.58    spl6_7 <=> m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.20/0.58  fof(f123,plain,(
% 0.20/0.58    spl6_8 <=> v1_funct_2(sK4,sK2,sK1)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.20/0.58  fof(f127,plain,(
% 0.20/0.58    spl6_9 <=> v1_funct_1(sK4)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.20/0.58  fof(f286,plain,(
% 0.20/0.58    spl6_35 <=> k1_xboole_0 = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.20/0.58  fof(f453,plain,(
% 0.20/0.58    spl6_55 <=> ! [X1] : (k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,sK2,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).
% 0.20/0.58  fof(f459,plain,(
% 0.20/0.58    ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_35 | ~spl6_55)),
% 0.20/0.58    inference(trivial_inequality_removal,[],[f458])).
% 0.20/0.58  fof(f458,plain,(
% 0.20/0.58    k1_xboole_0 != k1_xboole_0 | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_35 | ~spl6_55)),
% 0.20/0.58    inference(forward_demodulation,[],[f457,f287])).
% 0.20/0.58  fof(f287,plain,(
% 0.20/0.58    k1_xboole_0 = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | ~spl6_35),
% 0.20/0.58    inference(avatar_component_clause,[],[f286])).
% 0.20/0.58  fof(f457,plain,(
% 0.20/0.58    k1_xboole_0 != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | ~v1_funct_1(sK4) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_7 | ~spl6_8 | ~spl6_9 | ~spl6_55)),
% 0.20/0.58    inference(forward_demodulation,[],[f456,f208])).
% 0.20/0.58  fof(f208,plain,(
% 0.20/0.58    ( ! [X0] : (k2_partfun1(sK2,sK1,sK4,X0) = k7_relat_1(sK4,X0)) ) | (~spl6_7 | ~spl6_9)),
% 0.20/0.58    inference(resolution,[],[f195,f120])).
% 0.20/0.58  fof(f120,plain,(
% 0.20/0.58    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~spl6_7),
% 0.20/0.58    inference(avatar_component_clause,[],[f119])).
% 0.20/0.58  fof(f195,plain,(
% 0.20/0.58    ( ! [X4,X5,X3] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k2_partfun1(X3,X4,sK4,X5) = k7_relat_1(sK4,X5)) ) | ~spl6_9),
% 0.20/0.58    inference(resolution,[],[f83,f128])).
% 0.20/0.58  fof(f128,plain,(
% 0.20/0.58    v1_funct_1(sK4) | ~spl6_9),
% 0.20/0.58    inference(avatar_component_clause,[],[f127])).
% 0.20/0.58  fof(f83,plain,(
% 0.20/0.58    ( ! [X2,X0,X3,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f35])).
% 0.20/0.58  fof(f35,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 0.20/0.58    inference(flattening,[],[f34])).
% 0.20/0.58  fof(f34,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3] : (k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 0.20/0.58    inference(ennf_transformation,[],[f13])).
% 0.20/0.58  fof(f13,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => k2_partfun1(X0,X1,X2,X3) = k7_relat_1(X2,X3))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_partfun1)).
% 0.20/0.58  fof(f456,plain,(
% 0.20/0.58    ~v1_funct_1(sK4) | k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | (~spl6_8 | ~spl6_55)),
% 0.20/0.58    inference(resolution,[],[f454,f124])).
% 0.20/0.58  fof(f124,plain,(
% 0.20/0.58    v1_funct_2(sK4,sK2,sK1) | ~spl6_8),
% 0.20/0.58    inference(avatar_component_clause,[],[f123])).
% 0.20/0.58  fof(f454,plain,(
% 0.20/0.58    ( ! [X1] : (~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3)) ) | ~spl6_55),
% 0.20/0.58    inference(avatar_component_clause,[],[f453])).
% 0.20/0.58  fof(f455,plain,(
% 0.20/0.58    spl6_14 | spl6_55 | ~spl6_13 | ~spl6_33 | ~spl6_35 | ~spl6_53),
% 0.20/0.58    inference(avatar_split_clause,[],[f451,f441,f286,f274,f143,f453,f147])).
% 0.20/0.58  fof(f147,plain,(
% 0.20/0.58    spl6_14 <=> v1_xboole_0(sK2)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.20/0.58  fof(f143,plain,(
% 0.20/0.58    spl6_13 <=> m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 0.20/0.58  fof(f274,plain,(
% 0.20/0.58    spl6_33 <=> k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.20/0.58  fof(f441,plain,(
% 0.20/0.58    spl6_53 <=> ! [X1,X0] : (v1_xboole_0(X0) | sK5 = k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~v1_funct_2(X1,X0,sK1) | ~v1_funct_1(X1) | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0,sK3)) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 0.20/0.58  fof(f451,plain,(
% 0.20/0.58    ( ! [X1] : (k1_xboole_0 != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_xboole_0(sK2)) ) | (~spl6_13 | ~spl6_33 | ~spl6_35 | ~spl6_53)),
% 0.20/0.58    inference(forward_demodulation,[],[f450,f287])).
% 0.20/0.58  fof(f450,plain,(
% 0.20/0.58    ( ! [X1] : (k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | v1_xboole_0(sK2)) ) | (~spl6_13 | ~spl6_33 | ~spl6_53)),
% 0.20/0.58    inference(forward_demodulation,[],[f445,f275])).
% 0.20/0.58  fof(f275,plain,(
% 0.20/0.58    k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | ~spl6_33),
% 0.20/0.58    inference(avatar_component_clause,[],[f274])).
% 0.20/0.58  fof(f445,plain,(
% 0.20/0.58    ( ! [X1] : (sK5 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X1,sK5),sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(X1,sK2,sK1) | ~v1_funct_1(X1) | k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,X1,k9_subset_1(sK0,sK2,sK3)) | v1_xboole_0(sK2)) ) | (~spl6_13 | ~spl6_53)),
% 0.20/0.58    inference(resolution,[],[f442,f144])).
% 0.20/0.58  fof(f144,plain,(
% 0.20/0.58    m1_subset_1(sK2,k1_zfmisc_1(sK0)) | ~spl6_13),
% 0.20/0.58    inference(avatar_component_clause,[],[f143])).
% 0.20/0.58  fof(f442,plain,(
% 0.20/0.58    ( ! [X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(sK0)) | sK5 = k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~v1_funct_2(X1,X0,sK1) | ~v1_funct_1(X1) | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0,sK3)) | v1_xboole_0(X0)) ) | ~spl6_53),
% 0.20/0.58    inference(avatar_component_clause,[],[f441])).
% 0.20/0.58  fof(f443,plain,(
% 0.20/0.58    spl6_53 | spl6_16 | ~spl6_11 | ~spl6_52),
% 0.20/0.58    inference(avatar_split_clause,[],[f439,f436,f135,f155,f441])).
% 0.20/0.58  fof(f155,plain,(
% 0.20/0.58    spl6_16 <=> v1_xboole_0(sK0)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_16])])).
% 0.20/0.58  fof(f135,plain,(
% 0.20/0.58    spl6_11 <=> m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.20/0.58  fof(f436,plain,(
% 0.20/0.58    spl6_52 <=> ! [X1,X0,X2] : (k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3)) | v1_xboole_0(X2) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | ~m1_subset_1(sK3,k1_zfmisc_1(X2)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | sK5 = k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_52])])).
% 0.20/0.58  fof(f439,plain,(
% 0.20/0.58    ( ! [X0,X1] : (v1_xboole_0(sK0) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(sK0)) | k2_partfun1(X0,sK1,X1,k9_subset_1(sK0,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,X0,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | sK5 = k2_partfun1(k4_subset_1(sK0,X0,sK3),sK1,k1_tmap_1(sK0,sK1,X0,sK3,X1,sK5),sK3)) ) | (~spl6_11 | ~spl6_52)),
% 0.20/0.58    inference(resolution,[],[f437,f136])).
% 0.20/0.58  fof(f136,plain,(
% 0.20/0.58    m1_subset_1(sK3,k1_zfmisc_1(sK0)) | ~spl6_11),
% 0.20/0.58    inference(avatar_component_clause,[],[f135])).
% 0.20/0.58  fof(f437,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(sK3,k1_zfmisc_1(X2)) | v1_xboole_0(X2) | v1_xboole_0(X0) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3)) | ~v1_funct_1(X1) | ~v1_funct_2(X1,X0,sK1) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | sK5 = k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3)) ) | ~spl6_52),
% 0.20/0.58    inference(avatar_component_clause,[],[f436])).
% 0.20/0.58  fof(f438,plain,(
% 0.20/0.58    spl6_15 | spl6_12 | ~spl6_5 | spl6_52 | ~spl6_4 | ~spl6_6),
% 0.20/0.58    inference(avatar_split_clause,[],[f434,f115,f107,f436,f111,f139,f151])).
% 0.20/0.58  fof(f151,plain,(
% 0.20/0.58    spl6_15 <=> v1_xboole_0(sK1)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.20/0.58  fof(f139,plain,(
% 0.20/0.58    spl6_12 <=> v1_xboole_0(sK3)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.20/0.58  fof(f111,plain,(
% 0.20/0.58    spl6_5 <=> v1_funct_2(sK5,sK3,sK1)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.20/0.58  fof(f107,plain,(
% 0.20/0.58    spl6_4 <=> m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.20/0.58  fof(f115,plain,(
% 0.20/0.58    spl6_6 <=> v1_funct_1(sK5)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.20/0.58  fof(f434,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k7_relat_1(sK5,k9_subset_1(X2,X0,sK3)) | ~v1_funct_2(sK5,sK3,sK1) | sK5 = k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~v1_funct_2(X1,X0,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(X2)) | v1_xboole_0(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | v1_xboole_0(X0) | v1_xboole_0(sK1) | v1_xboole_0(X2)) ) | (~spl6_4 | ~spl6_6)),
% 0.20/0.58    inference(forward_demodulation,[],[f433,f197])).
% 0.20/0.58  fof(f197,plain,(
% 0.20/0.58    ( ! [X0] : (k2_partfun1(sK3,sK1,sK5,X0) = k7_relat_1(sK5,X0)) ) | (~spl6_4 | ~spl6_6)),
% 0.20/0.58    inference(resolution,[],[f194,f108])).
% 0.20/0.58  fof(f108,plain,(
% 0.20/0.58    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~spl6_4),
% 0.20/0.58    inference(avatar_component_clause,[],[f107])).
% 0.20/0.58  fof(f194,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_partfun1(X0,X1,sK5,X2) = k7_relat_1(sK5,X2)) ) | ~spl6_6),
% 0.20/0.58    inference(resolution,[],[f83,f116])).
% 0.20/0.58  fof(f116,plain,(
% 0.20/0.58    v1_funct_1(sK5) | ~spl6_6),
% 0.20/0.58    inference(avatar_component_clause,[],[f115])).
% 0.20/0.58  fof(f433,plain,(
% 0.20/0.58    ( ! [X2,X0,X1] : (k2_partfun1(X0,sK1,X1,k9_subset_1(X2,X0,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(X2,X0,sK3)) | ~v1_funct_2(sK5,sK3,sK1) | sK5 = k2_partfun1(k4_subset_1(X2,X0,sK3),sK1,k1_tmap_1(X2,sK1,X0,sK3,X1,sK5),sK3) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X0,sK1))) | ~v1_funct_2(X1,X0,sK1) | ~v1_funct_1(X1) | ~m1_subset_1(sK3,k1_zfmisc_1(X2)) | v1_xboole_0(sK3) | ~m1_subset_1(X0,k1_zfmisc_1(X2)) | v1_xboole_0(X0) | v1_xboole_0(sK1) | v1_xboole_0(X2)) ) | (~spl6_4 | ~spl6_6)),
% 0.20/0.58    inference(resolution,[],[f430,f108])).
% 0.20/0.58  fof(f430,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X3,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X4,X1))) | k2_partfun1(X0,X1,X2,k9_subset_1(X3,X0,X4)) != k2_partfun1(X4,X1,sK5,k9_subset_1(X3,X0,X4)) | ~v1_funct_2(sK5,X4,X1) | sK5 = k2_partfun1(k4_subset_1(X3,X0,X4),X1,k1_tmap_1(X3,X1,X0,X4,X2,sK5),X4) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X4,k1_zfmisc_1(X3)) | v1_xboole_0(X4) | ~m1_subset_1(X0,k1_zfmisc_1(X3)) | v1_xboole_0(X0) | v1_xboole_0(X1) | v1_xboole_0(X3)) ) | ~spl6_6),
% 0.20/0.58    inference(resolution,[],[f163,f116])).
% 0.20/0.58  fof(f163,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (~v1_funct_1(X5) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f161,f84])).
% 0.20/0.58  fof(f84,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f37])).
% 0.20/0.58  fof(f37,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.20/0.58    inference(flattening,[],[f36])).
% 0.20/0.58  fof(f36,plain,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.20/0.58    inference(ennf_transformation,[],[f15])).
% 0.20/0.58  fof(f15,axiom,(
% 0.20/0.58    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2) & ~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) & v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5))))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k1_tmap_1)).
% 0.20/0.58  fof(f161,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f159,f85])).
% 0.20/0.58  fof(f85,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f37])).
% 0.20/0.58  fof(f159,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f93,f86])).
% 0.20/0.58  fof(f86,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f37])).
% 0.20/0.58  fof(f93,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(equality_resolution,[],[f66])).
% 0.20/0.58  fof(f66,plain,(
% 0.20/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f46])).
% 0.20/0.58  fof(f46,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.58    inference(flattening,[],[f45])).
% 0.20/0.58  fof(f45,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : (((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 | (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) != X4)) & ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4) | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.58    inference(nnf_transformation,[],[f22])).
% 0.20/0.58  fof(f22,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : (! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5)) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4)) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3)) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2)) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.58    inference(flattening,[],[f21])).
% 0.20/0.58  fof(f21,plain,(
% 0.20/0.58    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (! [X4] : (! [X5] : ((! [X6] : ((k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4)) | (~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6))) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5))) | (~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4))) | (~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3))) | (~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2))) | v1_xboole_0(X1)) | v1_xboole_0(X0))),
% 0.20/0.58    inference(ennf_transformation,[],[f14])).
% 0.20/0.58  fof(f14,axiom,(
% 0.20/0.58    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) => ! [X6] : ((m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) & v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) & v1_funct_1(X6)) => (k1_tmap_1(X0,X1,X2,X3,X4,X5) = X6 <=> (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4))))))))))),
% 0.20/0.58    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tmap_1)).
% 0.20/0.58  fof(f428,plain,(
% 0.20/0.58    spl6_16 | spl6_15 | spl6_14 | ~spl6_13 | spl6_12 | ~spl6_11 | ~spl6_9 | ~spl6_8 | ~spl6_7 | ~spl6_6 | ~spl6_5 | ~spl6_4 | spl6_2 | ~spl6_4 | ~spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_33 | ~spl6_35),
% 0.20/0.58    inference(avatar_split_clause,[],[f423,f286,f274,f127,f119,f115,f107,f100,f107,f111,f115,f119,f123,f127,f135,f139,f143,f147,f151,f155])).
% 0.20/0.58  fof(f100,plain,(
% 0.20/0.58    spl6_2 <=> sK4 = k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.20/0.58  fof(f423,plain,(
% 0.20/0.58    ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (spl6_2 | ~spl6_4 | ~spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_33 | ~spl6_35)),
% 0.20/0.58    inference(trivial_inequality_removal,[],[f422])).
% 0.20/0.58  fof(f422,plain,(
% 0.20/0.58    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (spl6_2 | ~spl6_4 | ~spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_33 | ~spl6_35)),
% 0.20/0.58    inference(forward_demodulation,[],[f421,f287])).
% 0.20/0.58  fof(f421,plain,(
% 0.20/0.58    k1_xboole_0 != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (spl6_2 | ~spl6_4 | ~spl6_6 | ~spl6_7 | ~spl6_9 | ~spl6_33 | ~spl6_35)),
% 0.20/0.58    inference(forward_demodulation,[],[f420,f208])).
% 0.20/0.58  fof(f420,plain,(
% 0.20/0.58    k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (spl6_2 | ~spl6_4 | ~spl6_6 | ~spl6_33 | ~spl6_35)),
% 0.20/0.58    inference(forward_demodulation,[],[f419,f287])).
% 0.20/0.58  fof(f419,plain,(
% 0.20/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (spl6_2 | ~spl6_4 | ~spl6_6 | ~spl6_33)),
% 0.20/0.58    inference(forward_demodulation,[],[f418,f275])).
% 0.20/0.58  fof(f418,plain,(
% 0.20/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | (spl6_2 | ~spl6_4 | ~spl6_6)),
% 0.20/0.58    inference(forward_demodulation,[],[f417,f197])).
% 0.20/0.58  fof(f417,plain,(
% 0.20/0.58    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_2),
% 0.20/0.58    inference(trivial_inequality_removal,[],[f416])).
% 0.20/0.58  fof(f416,plain,(
% 0.20/0.58    sK4 != sK4 | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) | ~v1_funct_2(sK5,sK3,sK1) | ~v1_funct_1(sK5) | ~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) | ~v1_funct_2(sK4,sK2,sK1) | ~v1_funct_1(sK4) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | v1_xboole_0(sK3) | ~m1_subset_1(sK2,k1_zfmisc_1(sK0)) | v1_xboole_0(sK2) | v1_xboole_0(sK1) | v1_xboole_0(sK0) | spl6_2),
% 0.20/0.58    inference(superposition,[],[f101,f162])).
% 0.20/0.58  fof(f162,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f160,f84])).
% 0.20/0.58  fof(f160,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f158,f85])).
% 0.20/0.58  fof(f158,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(subsumption_resolution,[],[f94,f86])).
% 0.20/0.58  fof(f94,plain,(
% 0.20/0.58    ( ! [X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 | ~m1_subset_1(k1_tmap_1(X0,X1,X2,X3,X4,X5),k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(k1_tmap_1(X0,X1,X2,X3,X4,X5),k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(k1_tmap_1(X0,X1,X2,X3,X4,X5)) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(equality_resolution,[],[f65])).
% 0.20/0.58  fof(f65,plain,(
% 0.20/0.58    ( ! [X6,X4,X2,X0,X5,X3,X1] : (k2_partfun1(k4_subset_1(X0,X2,X3),X1,X6,X2) = X4 | k1_tmap_1(X0,X1,X2,X3,X4,X5) != X6 | ~m1_subset_1(X6,k1_zfmisc_1(k2_zfmisc_1(k4_subset_1(X0,X2,X3),X1))) | ~v1_funct_2(X6,k4_subset_1(X0,X2,X3),X1) | ~v1_funct_1(X6) | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3)) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) | ~v1_funct_2(X5,X3,X1) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) | ~v1_funct_2(X4,X2,X1) | ~v1_funct_1(X4) | ~m1_subset_1(X3,k1_zfmisc_1(X0)) | v1_xboole_0(X3) | ~m1_subset_1(X2,k1_zfmisc_1(X0)) | v1_xboole_0(X2) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.58    inference(cnf_transformation,[],[f46])).
% 0.20/0.58  fof(f101,plain,(
% 0.20/0.58    sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | spl6_2),
% 0.20/0.58    inference(avatar_component_clause,[],[f100])).
% 0.20/0.58  fof(f316,plain,(
% 0.20/0.58    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 0.20/0.58    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.58  fof(f311,plain,(
% 0.20/0.58    ~spl6_11 | ~spl6_7 | ~spl6_9 | ~spl6_18 | spl6_20 | ~spl6_25 | ~spl6_31),
% 0.20/0.58    inference(avatar_split_clause,[],[f310,f264,f222,f201,f180,f127,f119,f135])).
% 0.20/0.58  fof(f180,plain,(
% 0.20/0.58    spl6_18 <=> k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_18])])).
% 0.20/0.58  fof(f201,plain,(
% 0.20/0.58    spl6_20 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3))),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_20])])).
% 0.20/0.58  fof(f222,plain,(
% 0.20/0.58    spl6_25 <=> k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_25])])).
% 0.20/0.58  fof(f264,plain,(
% 0.20/0.58    spl6_31 <=> k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0)),
% 0.20/0.58    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.20/0.58  fof(f310,plain,(
% 0.20/0.58    ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | (~spl6_7 | ~spl6_9 | ~spl6_18 | spl6_20 | ~spl6_25 | ~spl6_31)),
% 0.20/0.58    inference(trivial_inequality_removal,[],[f309])).
% 0.20/0.59  % (25074)Refutation not found, incomplete strategy% (25074)------------------------------
% 0.20/0.59  % (25074)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.59  % (25074)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.59  
% 0.20/0.59  % (25074)Memory used [KB]: 11513
% 0.20/0.59  % (25074)Time elapsed: 0.124 s
% 0.20/0.59  % (25074)------------------------------
% 0.20/0.59  % (25074)------------------------------
% 0.20/0.60  % (25073)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.20/0.60  % (25061)Refutation not found, incomplete strategy% (25061)------------------------------
% 0.20/0.60  % (25061)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.60  % (25061)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.60  
% 0.20/0.60  % (25061)Memory used [KB]: 11385
% 0.20/0.60  % (25061)Time elapsed: 0.192 s
% 0.20/0.60  % (25061)------------------------------
% 0.20/0.60  % (25061)------------------------------
% 0.20/0.60  fof(f309,plain,(
% 0.20/0.60    k1_xboole_0 != k1_xboole_0 | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | (~spl6_7 | ~spl6_9 | ~spl6_18 | spl6_20 | ~spl6_25 | ~spl6_31)),
% 0.20/0.60    inference(forward_demodulation,[],[f308,f266])).
% 0.20/0.60  fof(f266,plain,(
% 0.20/0.60    k1_xboole_0 = k7_relat_1(sK4,k1_xboole_0) | ~spl6_25),
% 0.20/0.60    inference(avatar_component_clause,[],[f222])).
% 0.20/0.60  fof(f308,plain,(
% 0.20/0.60    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | (~spl6_7 | ~spl6_9 | ~spl6_18 | spl6_20 | ~spl6_31)),
% 0.20/0.60    inference(forward_demodulation,[],[f307,f208])).
% 0.20/0.60  fof(f307,plain,(
% 0.20/0.60    k1_xboole_0 != k2_partfun1(sK2,sK1,sK4,k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | (~spl6_18 | spl6_20 | ~spl6_31)),
% 0.20/0.60    inference(forward_demodulation,[],[f306,f265])).
% 0.20/0.60  fof(f265,plain,(
% 0.20/0.60    k1_xboole_0 = k7_relat_1(sK5,k1_xboole_0) | ~spl6_31),
% 0.20/0.60    inference(avatar_component_clause,[],[f264])).
% 0.20/0.60  fof(f306,plain,(
% 0.20/0.60    k2_partfun1(sK2,sK1,sK4,k1_xboole_0) != k7_relat_1(sK5,k1_xboole_0) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | (~spl6_18 | spl6_20)),
% 0.20/0.60    inference(forward_demodulation,[],[f304,f181])).
% 0.20/0.60  fof(f181,plain,(
% 0.20/0.60    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl6_18),
% 0.20/0.60    inference(avatar_component_clause,[],[f180])).
% 0.20/0.60  fof(f304,plain,(
% 0.20/0.60    k2_partfun1(sK2,sK1,sK4,k1_setfam_1(k2_tarski(sK2,sK3))) != k7_relat_1(sK5,k1_setfam_1(k2_tarski(sK2,sK3))) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | spl6_20),
% 0.20/0.60    inference(superposition,[],[f202,f90])).
% 0.20/0.60  fof(f90,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k1_setfam_1(k2_tarski(X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.60    inference(definition_unfolding,[],[f80,f71])).
% 0.20/0.60  fof(f71,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.60    inference(cnf_transformation,[],[f6])).
% 0.20/0.60  fof(f6,axiom,(
% 0.20/0.60    ! [X0,X1] : k3_xboole_0(X0,X1) = k1_setfam_1(k2_tarski(X0,X1))),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_setfam_1)).
% 0.20/0.60  fof(f80,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0))) )),
% 0.20/0.60    inference(cnf_transformation,[],[f31])).
% 0.20/0.60  fof(f31,plain,(
% 0.20/0.60    ! [X0,X1,X2] : (k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(X0)))),
% 0.20/0.60    inference(ennf_transformation,[],[f4])).
% 0.20/0.60  fof(f4,axiom,(
% 0.20/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(X0)) => k9_subset_1(X0,X1,X2) = k3_xboole_0(X1,X2))),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k9_subset_1)).
% 0.20/0.60  fof(f202,plain,(
% 0.20/0.60    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | spl6_20),
% 0.20/0.60    inference(avatar_component_clause,[],[f201])).
% 0.20/0.60  fof(f298,plain,(
% 0.20/0.60    ~spl6_11 | ~spl6_24 | ~spl6_18 | spl6_34),
% 0.20/0.60    inference(avatar_split_clause,[],[f297,f283,f180,f219,f135])).
% 0.20/0.60  fof(f219,plain,(
% 0.20/0.60    spl6_24 <=> r1_xboole_0(k1_xboole_0,k1_relat_1(sK5))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_24])])).
% 0.20/0.60  fof(f283,plain,(
% 0.20/0.60    spl6_34 <=> r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.20/0.60  fof(f297,plain,(
% 0.20/0.60    ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK5)) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | (~spl6_18 | spl6_34)),
% 0.20/0.60    inference(forward_demodulation,[],[f291,f181])).
% 0.20/0.60  fof(f291,plain,(
% 0.20/0.60    ~r1_xboole_0(k1_setfam_1(k2_tarski(sK2,sK3)),k1_relat_1(sK5)) | ~m1_subset_1(sK3,k1_zfmisc_1(sK0)) | spl6_34),
% 0.20/0.60    inference(superposition,[],[f284,f90])).
% 0.20/0.60  fof(f284,plain,(
% 0.20/0.60    ~r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5)) | spl6_34),
% 0.20/0.60    inference(avatar_component_clause,[],[f283])).
% 0.20/0.60  fof(f289,plain,(
% 0.20/0.60    ~spl6_23 | ~spl6_34 | spl6_35 | ~spl6_33),
% 0.20/0.60    inference(avatar_split_clause,[],[f279,f274,f286,f283,f216])).
% 0.20/0.60  fof(f216,plain,(
% 0.20/0.60    spl6_23 <=> v1_relat_1(sK5)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_23])])).
% 0.20/0.60  fof(f279,plain,(
% 0.20/0.60    k1_xboole_0 = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | ~r1_xboole_0(k9_subset_1(sK0,sK2,sK3),k1_relat_1(sK5)) | ~v1_relat_1(sK5) | ~spl6_33),
% 0.20/0.60    inference(superposition,[],[f68,f275])).
% 0.20/0.60  fof(f68,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f23])).
% 0.20/0.60  fof(f23,plain,(
% 0.20/0.60    ! [X0] : (! [X1] : (k1_xboole_0 = k7_relat_1(X0,X1) | ~r1_xboole_0(X1,k1_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.60    inference(ennf_transformation,[],[f7])).
% 0.20/0.60  fof(f7,axiom,(
% 0.20/0.60    ! [X0] : (v1_relat_1(X0) => ! [X1] : (r1_xboole_0(X1,k1_relat_1(X0)) => k1_xboole_0 = k7_relat_1(X0,X1)))),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t187_relat_1)).
% 0.20/0.60  fof(f276,plain,(
% 0.20/0.60    spl6_33 | ~spl6_1 | ~spl6_4 | ~spl6_6 | ~spl6_7 | ~spl6_9),
% 0.20/0.60    inference(avatar_split_clause,[],[f272,f127,f119,f115,f107,f97,f274])).
% 0.20/0.60  fof(f97,plain,(
% 0.20/0.60    spl6_1 <=> k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.20/0.60  fof(f272,plain,(
% 0.20/0.60    k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK4,k9_subset_1(sK0,sK2,sK3)) | (~spl6_1 | ~spl6_4 | ~spl6_6 | ~spl6_7 | ~spl6_9)),
% 0.20/0.60    inference(forward_demodulation,[],[f271,f208])).
% 0.20/0.60  fof(f271,plain,(
% 0.20/0.60    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | (~spl6_1 | ~spl6_4 | ~spl6_6)),
% 0.20/0.60    inference(forward_demodulation,[],[f259,f197])).
% 0.20/0.60  fof(f259,plain,(
% 0.20/0.60    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) = k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | ~spl6_1),
% 0.20/0.60    inference(avatar_component_clause,[],[f97])).
% 0.20/0.60  fof(f258,plain,(
% 0.20/0.60    spl6_29),
% 0.20/0.60    inference(avatar_contradiction_clause,[],[f257])).
% 0.20/0.60  fof(f257,plain,(
% 0.20/0.60    $false | spl6_29),
% 0.20/0.60    inference(trivial_inequality_removal,[],[f256])).
% 0.20/0.60  fof(f256,plain,(
% 0.20/0.60    k1_xboole_0 != k1_xboole_0 | spl6_29),
% 0.20/0.60    inference(superposition,[],[f253,f164])).
% 0.20/0.60  fof(f164,plain,(
% 0.20/0.60    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,X0))) )),
% 0.20/0.60    inference(superposition,[],[f87,f70])).
% 0.20/0.60  fof(f70,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k2_tarski(X0,X1) = k2_tarski(X1,X0)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f3])).
% 0.20/0.60  fof(f3,axiom,(
% 0.20/0.60    ! [X0,X1] : k2_tarski(X0,X1) = k2_tarski(X1,X0)),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).
% 0.20/0.60  fof(f87,plain,(
% 0.20/0.60    ( ! [X0] : (k1_xboole_0 = k1_setfam_1(k2_tarski(X0,k1_xboole_0))) )),
% 0.20/0.60    inference(definition_unfolding,[],[f64,f71])).
% 0.20/0.60  fof(f64,plain,(
% 0.20/0.60    ( ! [X0] : (k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f2])).
% 0.20/0.60  fof(f2,axiom,(
% 0.20/0.60    ! [X0] : k1_xboole_0 = k3_xboole_0(X0,k1_xboole_0)),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).
% 0.20/0.60  fof(f253,plain,(
% 0.20/0.60    k1_xboole_0 != k1_setfam_1(k2_tarski(k1_xboole_0,k1_relat_1(sK4))) | spl6_29),
% 0.20/0.60    inference(avatar_component_clause,[],[f252])).
% 0.20/0.60  fof(f252,plain,(
% 0.20/0.60    spl6_29 <=> k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,k1_relat_1(sK4)))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.20/0.60  fof(f254,plain,(
% 0.20/0.60    ~spl6_29 | spl6_28),
% 0.20/0.60    inference(avatar_split_clause,[],[f250,f244,f252])).
% 0.20/0.60  fof(f244,plain,(
% 0.20/0.60    spl6_28 <=> r1_xboole_0(k1_xboole_0,k1_relat_1(sK4))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_28])])).
% 0.20/0.60  fof(f250,plain,(
% 0.20/0.60    k1_xboole_0 != k1_setfam_1(k2_tarski(k1_xboole_0,k1_relat_1(sK4))) | spl6_28),
% 0.20/0.60    inference(resolution,[],[f245,f88])).
% 0.20/0.60  fof(f88,plain,(
% 0.20/0.60    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k1_xboole_0 != k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.60    inference(definition_unfolding,[],[f79,f71])).
% 0.20/0.60  fof(f79,plain,(
% 0.20/0.60    ( ! [X0,X1] : (r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) )),
% 0.20/0.60    inference(cnf_transformation,[],[f49])).
% 0.20/0.60  fof(f49,plain,(
% 0.20/0.60    ! [X0,X1] : ((r1_xboole_0(X0,X1) | k3_xboole_0(X0,X1) != k1_xboole_0) & (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)))),
% 0.20/0.60    inference(nnf_transformation,[],[f1])).
% 0.20/0.60  fof(f1,axiom,(
% 0.20/0.60    ! [X0,X1] : (r1_xboole_0(X0,X1) <=> k3_xboole_0(X0,X1) = k1_xboole_0)),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).
% 0.20/0.60  fof(f245,plain,(
% 0.20/0.60    ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK4)) | spl6_28),
% 0.20/0.60    inference(avatar_component_clause,[],[f244])).
% 0.20/0.60  fof(f249,plain,(
% 0.20/0.60    ~spl6_7 | spl6_27),
% 0.20/0.60    inference(avatar_contradiction_clause,[],[f248])).
% 0.20/0.60  fof(f248,plain,(
% 0.20/0.60    $false | (~spl6_7 | spl6_27)),
% 0.20/0.60    inference(subsumption_resolution,[],[f120,f247])).
% 0.20/0.60  fof(f247,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_27),
% 0.20/0.60    inference(resolution,[],[f242,f81])).
% 0.20/0.60  fof(f81,plain,(
% 0.20/0.60    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.60    inference(cnf_transformation,[],[f32])).
% 0.20/0.60  fof(f32,plain,(
% 0.20/0.60    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.60    inference(ennf_transformation,[],[f9])).
% 0.20/0.60  fof(f9,axiom,(
% 0.20/0.60    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.60  fof(f242,plain,(
% 0.20/0.60    ~v1_relat_1(sK4) | spl6_27),
% 0.20/0.60    inference(avatar_component_clause,[],[f241])).
% 0.20/0.60  fof(f241,plain,(
% 0.20/0.60    spl6_27 <=> v1_relat_1(sK4)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_27])])).
% 0.20/0.60  fof(f246,plain,(
% 0.20/0.60    ~spl6_27 | ~spl6_28 | spl6_25),
% 0.20/0.60    inference(avatar_split_clause,[],[f239,f222,f244,f241])).
% 0.20/0.60  fof(f239,plain,(
% 0.20/0.60    ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl6_25),
% 0.20/0.60    inference(trivial_inequality_removal,[],[f238])).
% 0.20/0.60  fof(f238,plain,(
% 0.20/0.60    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK4)) | ~v1_relat_1(sK4) | spl6_25),
% 0.20/0.60    inference(superposition,[],[f223,f68])).
% 0.20/0.60  fof(f223,plain,(
% 0.20/0.60    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | spl6_25),
% 0.20/0.60    inference(avatar_component_clause,[],[f222])).
% 0.20/0.60  fof(f236,plain,(
% 0.20/0.60    spl6_26),
% 0.20/0.60    inference(avatar_contradiction_clause,[],[f235])).
% 0.20/0.60  fof(f235,plain,(
% 0.20/0.60    $false | spl6_26),
% 0.20/0.60    inference(trivial_inequality_removal,[],[f234])).
% 0.20/0.60  fof(f234,plain,(
% 0.20/0.60    k1_xboole_0 != k1_xboole_0 | spl6_26),
% 0.20/0.60    inference(superposition,[],[f231,f164])).
% 0.20/0.60  fof(f231,plain,(
% 0.20/0.60    k1_xboole_0 != k1_setfam_1(k2_tarski(k1_xboole_0,k1_relat_1(sK5))) | spl6_26),
% 0.20/0.60    inference(avatar_component_clause,[],[f230])).
% 0.20/0.60  fof(f230,plain,(
% 0.20/0.60    spl6_26 <=> k1_xboole_0 = k1_setfam_1(k2_tarski(k1_xboole_0,k1_relat_1(sK5)))),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_26])])).
% 0.20/0.60  fof(f232,plain,(
% 0.20/0.60    ~spl6_26 | spl6_24),
% 0.20/0.60    inference(avatar_split_clause,[],[f228,f219,f230])).
% 0.20/0.60  fof(f228,plain,(
% 0.20/0.60    k1_xboole_0 != k1_setfam_1(k2_tarski(k1_xboole_0,k1_relat_1(sK5))) | spl6_24),
% 0.20/0.60    inference(resolution,[],[f220,f88])).
% 0.20/0.60  fof(f220,plain,(
% 0.20/0.60    ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK5)) | spl6_24),
% 0.20/0.60    inference(avatar_component_clause,[],[f219])).
% 0.20/0.60  fof(f227,plain,(
% 0.20/0.60    ~spl6_4 | spl6_23),
% 0.20/0.60    inference(avatar_contradiction_clause,[],[f226])).
% 0.20/0.60  fof(f226,plain,(
% 0.20/0.60    $false | (~spl6_4 | spl6_23)),
% 0.20/0.60    inference(subsumption_resolution,[],[f108,f225])).
% 0.20/0.60  fof(f225,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl6_23),
% 0.20/0.60    inference(resolution,[],[f217,f81])).
% 0.20/0.60  fof(f217,plain,(
% 0.20/0.60    ~v1_relat_1(sK5) | spl6_23),
% 0.20/0.60    inference(avatar_component_clause,[],[f216])).
% 0.20/0.60  fof(f224,plain,(
% 0.20/0.60    ~spl6_23 | ~spl6_24 | ~spl6_25 | spl6_22),
% 0.20/0.60    inference(avatar_split_clause,[],[f214,f211,f222,f219,f216])).
% 0.20/0.60  fof(f211,plain,(
% 0.20/0.60    spl6_22 <=> k7_relat_1(sK5,k1_xboole_0) = k7_relat_1(sK4,k1_xboole_0)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_22])])).
% 0.20/0.60  fof(f214,plain,(
% 0.20/0.60    k1_xboole_0 != k7_relat_1(sK4,k1_xboole_0) | ~r1_xboole_0(k1_xboole_0,k1_relat_1(sK5)) | ~v1_relat_1(sK5) | spl6_22),
% 0.20/0.60    inference(superposition,[],[f212,f68])).
% 0.20/0.60  fof(f212,plain,(
% 0.20/0.60    k7_relat_1(sK5,k1_xboole_0) != k7_relat_1(sK4,k1_xboole_0) | spl6_22),
% 0.20/0.60    inference(avatar_component_clause,[],[f211])).
% 0.20/0.60  fof(f203,plain,(
% 0.20/0.60    ~spl6_20 | spl6_1 | ~spl6_4 | ~spl6_6),
% 0.20/0.60    inference(avatar_split_clause,[],[f198,f115,f107,f97,f201])).
% 0.20/0.60  fof(f198,plain,(
% 0.20/0.60    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k7_relat_1(sK5,k9_subset_1(sK0,sK2,sK3)) | (spl6_1 | ~spl6_4 | ~spl6_6)),
% 0.20/0.60    inference(superposition,[],[f98,f197])).
% 0.20/0.60  fof(f98,plain,(
% 0.20/0.60    k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3)) | spl6_1),
% 0.20/0.60    inference(avatar_component_clause,[],[f97])).
% 0.20/0.60  fof(f182,plain,(
% 0.20/0.60    spl6_18 | ~spl6_17),
% 0.20/0.60    inference(avatar_split_clause,[],[f178,f173,f180])).
% 0.20/0.60  fof(f173,plain,(
% 0.20/0.60    spl6_17 <=> r1_xboole_0(sK2,sK3)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_17])])).
% 0.20/0.60  fof(f178,plain,(
% 0.20/0.60    k1_xboole_0 = k1_setfam_1(k2_tarski(sK2,sK3)) | ~spl6_17),
% 0.20/0.60    inference(resolution,[],[f174,f89])).
% 0.20/0.60  fof(f89,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~r1_xboole_0(X0,X1) | k1_xboole_0 = k1_setfam_1(k2_tarski(X0,X1))) )),
% 0.20/0.60    inference(definition_unfolding,[],[f78,f71])).
% 0.20/0.60  fof(f78,plain,(
% 0.20/0.60    ( ! [X0,X1] : (k3_xboole_0(X0,X1) = k1_xboole_0 | ~r1_xboole_0(X0,X1)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f49])).
% 0.20/0.60  fof(f174,plain,(
% 0.20/0.60    r1_xboole_0(sK2,sK3) | ~spl6_17),
% 0.20/0.60    inference(avatar_component_clause,[],[f173])).
% 0.20/0.60  fof(f175,plain,(
% 0.20/0.60    spl6_14 | spl6_12 | spl6_17 | ~spl6_10),
% 0.20/0.60    inference(avatar_split_clause,[],[f169,f131,f173,f139,f147])).
% 0.20/0.60  fof(f131,plain,(
% 0.20/0.60    spl6_10 <=> r1_subset_1(sK2,sK3)),
% 0.20/0.60    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.20/0.60  fof(f169,plain,(
% 0.20/0.60    r1_xboole_0(sK2,sK3) | v1_xboole_0(sK3) | v1_xboole_0(sK2) | ~spl6_10),
% 0.20/0.60    inference(resolution,[],[f74,f132])).
% 0.20/0.60  fof(f132,plain,(
% 0.20/0.60    r1_subset_1(sK2,sK3) | ~spl6_10),
% 0.20/0.60    inference(avatar_component_clause,[],[f131])).
% 0.20/0.60  fof(f74,plain,(
% 0.20/0.60    ( ! [X0,X1] : (~r1_subset_1(X0,X1) | r1_xboole_0(X0,X1) | v1_xboole_0(X1) | v1_xboole_0(X0)) )),
% 0.20/0.60    inference(cnf_transformation,[],[f47])).
% 0.20/0.60  fof(f47,plain,(
% 0.20/0.60    ! [X0,X1] : (((r1_subset_1(X0,X1) | ~r1_xboole_0(X0,X1)) & (r1_xboole_0(X0,X1) | ~r1_subset_1(X0,X1))) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.20/0.60    inference(nnf_transformation,[],[f28])).
% 0.20/0.60  fof(f28,plain,(
% 0.20/0.60    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | v1_xboole_0(X1) | v1_xboole_0(X0))),
% 0.20/0.60    inference(flattening,[],[f27])).
% 0.20/0.60  fof(f27,plain,(
% 0.20/0.60    ! [X0,X1] : ((r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)) | (v1_xboole_0(X1) | v1_xboole_0(X0)))),
% 0.20/0.60    inference(ennf_transformation,[],[f8])).
% 0.20/0.60  fof(f8,axiom,(
% 0.20/0.60    ! [X0,X1] : ((~v1_xboole_0(X1) & ~v1_xboole_0(X0)) => (r1_subset_1(X0,X1) <=> r1_xboole_0(X0,X1)))),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r1_subset_1)).
% 0.20/0.60  fof(f157,plain,(
% 0.20/0.60    ~spl6_16),
% 0.20/0.60    inference(avatar_split_clause,[],[f50,f155])).
% 0.20/0.60  fof(f50,plain,(
% 0.20/0.60    ~v1_xboole_0(sK0)),
% 0.20/0.60    inference(cnf_transformation,[],[f44])).
% 0.20/0.60  fof(f44,plain,(
% 0.20/0.60    ((((((sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2)) & ~v1_xboole_0(sK1)) & ~v1_xboole_0(sK0)),
% 0.20/0.60    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2,sK3,sK4,sK5])],[f20,f43,f42,f41,f40,f39,f38])).
% 0.20/0.60  fof(f38,plain,(
% 0.20/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0)) => (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(sK0))),
% 0.20/0.60    introduced(choice_axiom,[])).
% 0.20/0.60  fof(f39,plain,(
% 0.20/0.60    ? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),X1,k1_tmap_1(sK0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) => (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(sK1))),
% 0.20/0.60    introduced(choice_axiom,[])).
% 0.20/0.60  fof(f40,plain,(
% 0.20/0.60    ? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,X2,X3),sK1,k1_tmap_1(sK0,sK1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,sK1,X4,k9_subset_1(sK0,X2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,sK1))) & v1_funct_2(X4,X2,sK1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X2)) => (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) & m1_subset_1(sK2,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK2))),
% 0.20/0.60    introduced(choice_axiom,[])).
% 0.20/0.60  fof(f41,plain,(
% 0.20/0.60    ? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,X3),sK1,k1_tmap_1(sK0,sK1,sK2,X3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,X3)) != k2_partfun1(X3,sK1,X5,k9_subset_1(sK0,sK2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,sK1))) & v1_funct_2(X5,X3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,X3) & m1_subset_1(X3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(X3)) => (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) & r1_subset_1(sK2,sK3) & m1_subset_1(sK3,k1_zfmisc_1(sK0)) & ~v1_xboole_0(sK3))),
% 0.20/0.60    introduced(choice_axiom,[])).
% 0.20/0.60  fof(f42,plain,(
% 0.20/0.60    ? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK3) != X5 | k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,X4,X5),sK2) != X4 | k2_partfun1(sK2,sK1,X4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(X4,sK2,sK1) & v1_funct_1(X4)) => (? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5 | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2) | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) & m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1))) & v1_funct_2(sK4,sK2,sK1) & v1_funct_1(sK4))),
% 0.20/0.60    introduced(choice_axiom,[])).
% 0.20/0.60  fof(f43,plain,(
% 0.20/0.60    ? [X5] : ((k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK3) != X5 | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,X5),sK2) | k2_partfun1(sK3,sK1,X5,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(X5,sK3,sK1) & v1_funct_1(X5)) => ((sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))) & m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1))) & v1_funct_2(sK5,sK3,sK1) & v1_funct_1(sK5))),
% 0.20/0.60    introduced(choice_axiom,[])).
% 0.20/0.60  fof(f20,plain,(
% 0.20/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : (? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) & r1_subset_1(X2,X3) & m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) & m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.60    inference(flattening,[],[f19])).
% 0.20/0.60  fof(f19,plain,(
% 0.20/0.60    ? [X0] : (? [X1] : (? [X2] : (? [X3] : ((? [X4] : (? [X5] : ((k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) != X5 | k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) != X4 | k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) != k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))) & (m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5))) & (m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4))) & r1_subset_1(X2,X3)) & (m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3))) & (m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2))) & ~v1_xboole_0(X1)) & ~v1_xboole_0(X0))),
% 0.20/0.60    inference(ennf_transformation,[],[f17])).
% 0.20/0.60  fof(f17,negated_conjecture,(
% 0.20/0.60    ~! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 0.20/0.60    inference(negated_conjecture,[],[f16])).
% 0.20/0.60  fof(f16,conjecture,(
% 0.20/0.60    ! [X0] : (~v1_xboole_0(X0) => ! [X1] : (~v1_xboole_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(X0)) & ~v1_xboole_0(X2)) => ! [X3] : ((m1_subset_1(X3,k1_zfmisc_1(X0)) & ~v1_xboole_0(X3)) => (r1_subset_1(X2,X3) => ! [X4] : ((m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X2,X1))) & v1_funct_2(X4,X2,X1) & v1_funct_1(X4)) => ! [X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X1))) & v1_funct_2(X5,X3,X1) & v1_funct_1(X5)) => (k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X3) = X5 & k2_partfun1(k4_subset_1(X0,X2,X3),X1,k1_tmap_1(X0,X1,X2,X3,X4,X5),X2) = X4 & k2_partfun1(X2,X1,X4,k9_subset_1(X0,X2,X3)) = k2_partfun1(X3,X1,X5,k9_subset_1(X0,X2,X3))))))))))),
% 0.20/0.60    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_tmap_1)).
% 0.20/0.60  fof(f153,plain,(
% 0.20/0.60    ~spl6_15),
% 0.20/0.60    inference(avatar_split_clause,[],[f51,f151])).
% 0.20/0.60  fof(f51,plain,(
% 0.20/0.60    ~v1_xboole_0(sK1)),
% 0.20/0.60    inference(cnf_transformation,[],[f44])).
% 0.20/0.60  fof(f149,plain,(
% 0.20/0.60    ~spl6_14),
% 0.20/0.60    inference(avatar_split_clause,[],[f52,f147])).
% 0.20/0.60  fof(f52,plain,(
% 0.20/0.60    ~v1_xboole_0(sK2)),
% 0.20/0.60    inference(cnf_transformation,[],[f44])).
% 0.20/0.60  fof(f145,plain,(
% 0.20/0.60    spl6_13),
% 0.20/0.60    inference(avatar_split_clause,[],[f53,f143])).
% 0.20/0.60  fof(f53,plain,(
% 0.20/0.60    m1_subset_1(sK2,k1_zfmisc_1(sK0))),
% 0.20/0.60    inference(cnf_transformation,[],[f44])).
% 0.20/0.60  fof(f141,plain,(
% 0.20/0.60    ~spl6_12),
% 0.20/0.60    inference(avatar_split_clause,[],[f54,f139])).
% 0.20/0.60  fof(f54,plain,(
% 0.20/0.60    ~v1_xboole_0(sK3)),
% 0.20/0.60    inference(cnf_transformation,[],[f44])).
% 0.20/0.60  fof(f137,plain,(
% 0.20/0.60    spl6_11),
% 0.20/0.60    inference(avatar_split_clause,[],[f55,f135])).
% 0.20/0.60  fof(f55,plain,(
% 0.20/0.60    m1_subset_1(sK3,k1_zfmisc_1(sK0))),
% 0.20/0.60    inference(cnf_transformation,[],[f44])).
% 0.20/0.60  fof(f133,plain,(
% 0.20/0.60    spl6_10),
% 0.20/0.60    inference(avatar_split_clause,[],[f56,f131])).
% 0.20/0.60  fof(f56,plain,(
% 0.20/0.60    r1_subset_1(sK2,sK3)),
% 0.20/0.60    inference(cnf_transformation,[],[f44])).
% 0.20/0.60  fof(f129,plain,(
% 0.20/0.60    spl6_9),
% 0.20/0.60    inference(avatar_split_clause,[],[f57,f127])).
% 0.20/0.60  fof(f57,plain,(
% 0.20/0.60    v1_funct_1(sK4)),
% 0.20/0.60    inference(cnf_transformation,[],[f44])).
% 0.20/0.60  fof(f125,plain,(
% 0.20/0.60    spl6_8),
% 0.20/0.60    inference(avatar_split_clause,[],[f58,f123])).
% 0.20/0.60  fof(f58,plain,(
% 0.20/0.60    v1_funct_2(sK4,sK2,sK1)),
% 0.20/0.60    inference(cnf_transformation,[],[f44])).
% 0.20/0.60  fof(f121,plain,(
% 0.20/0.60    spl6_7),
% 0.20/0.60    inference(avatar_split_clause,[],[f59,f119])).
% 0.20/0.60  fof(f59,plain,(
% 0.20/0.60    m1_subset_1(sK4,k1_zfmisc_1(k2_zfmisc_1(sK2,sK1)))),
% 0.20/0.60    inference(cnf_transformation,[],[f44])).
% 0.20/0.60  fof(f117,plain,(
% 0.20/0.60    spl6_6),
% 0.20/0.60    inference(avatar_split_clause,[],[f60,f115])).
% 0.20/0.60  fof(f60,plain,(
% 0.20/0.60    v1_funct_1(sK5)),
% 0.20/0.60    inference(cnf_transformation,[],[f44])).
% 0.20/0.60  fof(f113,plain,(
% 0.20/0.60    spl6_5),
% 0.20/0.60    inference(avatar_split_clause,[],[f61,f111])).
% 0.20/0.60  fof(f61,plain,(
% 0.20/0.60    v1_funct_2(sK5,sK3,sK1)),
% 0.20/0.60    inference(cnf_transformation,[],[f44])).
% 0.20/0.60  fof(f109,plain,(
% 0.20/0.60    spl6_4),
% 0.20/0.60    inference(avatar_split_clause,[],[f62,f107])).
% 0.20/0.60  fof(f62,plain,(
% 0.20/0.60    m1_subset_1(sK5,k1_zfmisc_1(k2_zfmisc_1(sK3,sK1)))),
% 0.20/0.60    inference(cnf_transformation,[],[f44])).
% 0.20/0.60  fof(f105,plain,(
% 0.20/0.60    ~spl6_1 | ~spl6_2 | ~spl6_3),
% 0.20/0.60    inference(avatar_split_clause,[],[f63,f103,f100,f97])).
% 0.20/0.60  fof(f63,plain,(
% 0.20/0.60    sK5 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK3) | sK4 != k2_partfun1(k4_subset_1(sK0,sK2,sK3),sK1,k1_tmap_1(sK0,sK1,sK2,sK3,sK4,sK5),sK2) | k2_partfun1(sK2,sK1,sK4,k9_subset_1(sK0,sK2,sK3)) != k2_partfun1(sK3,sK1,sK5,k9_subset_1(sK0,sK2,sK3))),
% 0.20/0.60    inference(cnf_transformation,[],[f44])).
% 0.20/0.60  % SZS output end Proof for theBenchmark
% 0.20/0.60  % (25071)------------------------------
% 0.20/0.60  % (25071)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.60  % (25071)Termination reason: Refutation
% 0.20/0.60  
% 0.20/0.60  % (25071)Memory used [KB]: 11257
% 0.20/0.60  % (25071)Time elapsed: 0.157 s
% 0.20/0.60  % (25071)------------------------------
% 0.20/0.60  % (25071)------------------------------
% 0.20/0.61  % (25050)Success in time 0.245 s
%------------------------------------------------------------------------------
