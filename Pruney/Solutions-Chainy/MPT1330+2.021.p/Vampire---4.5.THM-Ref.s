%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  184 ( 340 expanded)
%              Number of leaves         :   48 ( 158 expanded)
%              Depth                    :    6
%              Number of atoms          :  541 (1058 expanded)
%              Number of equality atoms :   93 ( 236 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f327,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f56,f60,f64,f68,f75,f79,f83,f87,f91,f95,f99,f103,f119,f123,f131,f135,f147,f155,f159,f165,f173,f178,f182,f190,f194,f203,f211,f226,f235,f238,f241,f288,f304,f306,f318,f326])).

fof(f326,plain,
    ( ~ spl3_39
    | ~ spl3_8
    | ~ spl3_22
    | spl3_51 ),
    inference(avatar_split_clause,[],[f321,f316,f145,f81,f230])).

fof(f230,plain,
    ( spl3_39
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f81,plain,
    ( spl3_8
  <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f145,plain,
    ( spl3_22
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ r1_xboole_0(k2_relat_1(X1),X0)
        | k1_xboole_0 = k10_relat_1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f316,plain,
    ( spl3_51
  <=> k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f321,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_8
    | ~ spl3_22
    | spl3_51 ),
    inference(subsumption_resolution,[],[f320,f82])).

fof(f82,plain,
    ( ! [X0] : r1_xboole_0(X0,k1_xboole_0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f81])).

fof(f320,plain,
    ( ~ r1_xboole_0(k2_relat_1(sK2),k1_xboole_0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_22
    | spl3_51 ),
    inference(trivial_inequality_removal,[],[f319])).

fof(f319,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ r1_xboole_0(k2_relat_1(sK2),k1_xboole_0)
    | ~ v1_relat_1(sK2)
    | ~ spl3_22
    | spl3_51 ),
    inference(superposition,[],[f317,f146])).

fof(f146,plain,
    ( ! [X0,X1] :
        ( k1_xboole_0 = k10_relat_1(X1,X0)
        | ~ r1_xboole_0(k2_relat_1(X1),X0)
        | ~ v1_relat_1(X1) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f145])).

fof(f317,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,k1_xboole_0)
    | spl3_51 ),
    inference(avatar_component_clause,[],[f316])).

fof(f318,plain,
    ( ~ spl3_51
    | spl3_45
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f307,f302,f286,f316])).

fof(f286,plain,
    ( spl3_45
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f302,plain,
    ( spl3_49
  <=> ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f307,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,k1_xboole_0)
    | spl3_45
    | ~ spl3_49 ),
    inference(superposition,[],[f287,f303])).

fof(f303,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,X0)
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f302])).

fof(f287,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)
    | spl3_45 ),
    inference(avatar_component_clause,[],[f286])).

fof(f306,plain,
    ( spl3_6
    | ~ spl3_11
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f243,f224,f93,f73])).

fof(f73,plain,
    ( spl3_6
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f93,plain,
    ( spl3_11
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f224,plain,
    ( spl3_38
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f243,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_11
    | ~ spl3_38 ),
    inference(resolution,[],[f225,f94])).

fof(f94,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f93])).

fof(f225,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f224])).

fof(f304,plain,
    ( spl3_49
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_30
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f262,f224,f180,f93,f70,f302])).

fof(f70,plain,
    ( spl3_5
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f180,plain,
    ( spl3_30
  <=> ! [X0] : k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f262,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,X0)
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_30
    | ~ spl3_38 ),
    inference(backward_demodulation,[],[f251,f71])).

fof(f71,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f70])).

fof(f251,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2,X0)
    | ~ spl3_11
    | ~ spl3_30
    | ~ spl3_38 ),
    inference(backward_demodulation,[],[f181,f243])).

fof(f181,plain,
    ( ! [X0] : k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f180])).

fof(f288,plain,
    ( ~ spl3_45
    | ~ spl3_5
    | ~ spl3_11
    | spl3_18
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f261,f224,f129,f93,f70,f286])).

fof(f129,plain,
    ( spl3_18
  <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f261,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_11
    | spl3_18
    | ~ spl3_38 ),
    inference(backward_demodulation,[],[f250,f71])).

fof(f250,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl3_11
    | spl3_18
    | ~ spl3_38 ),
    inference(backward_demodulation,[],[f130,f243])).

fof(f130,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f129])).

fof(f241,plain,
    ( ~ spl3_16
    | ~ spl3_19
    | spl3_40 ),
    inference(avatar_contradiction_clause,[],[f239])).

fof(f239,plain,
    ( $false
    | ~ spl3_16
    | ~ spl3_19
    | spl3_40 ),
    inference(unit_resulting_resolution,[],[f122,f234,f134])).

fof(f134,plain,
    ( ! [X2,X0,X1] :
        ( v4_relat_1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f133])).

fof(f133,plain,
    ( spl3_19
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v4_relat_1(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f234,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | spl3_40 ),
    inference(avatar_component_clause,[],[f233])).

fof(f233,plain,
    ( spl3_40
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f122,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f121])).

fof(f121,plain,
    ( spl3_16
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f238,plain,
    ( ~ spl3_10
    | ~ spl3_13
    | ~ spl3_16
    | spl3_39 ),
    inference(avatar_contradiction_clause,[],[f236])).

fof(f236,plain,
    ( $false
    | ~ spl3_10
    | ~ spl3_13
    | ~ spl3_16
    | spl3_39 ),
    inference(unit_resulting_resolution,[],[f90,f122,f231,f102])).

fof(f102,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f101])).

fof(f101,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f231,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_39 ),
    inference(avatar_component_clause,[],[f230])).

fof(f90,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f89])).

fof(f89,plain,
    ( spl3_10
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f235,plain,
    ( ~ spl3_39
    | ~ spl3_40
    | ~ spl3_24
    | spl3_33
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f228,f221,f201,f153,f233,f230])).

fof(f153,plain,
    ( spl3_24
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ v4_relat_1(X1,X0)
        | k1_relat_1(X1) = X0
        | ~ v1_partfun1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f201,plain,
    ( spl3_33
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f221,plain,
    ( spl3_37
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f228,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl3_24
    | spl3_33
    | ~ spl3_37 ),
    inference(subsumption_resolution,[],[f227,f202])).

fof(f202,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | spl3_33 ),
    inference(avatar_component_clause,[],[f201])).

fof(f227,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_24
    | ~ spl3_37 ),
    inference(resolution,[],[f222,f154])).

fof(f154,plain,
    ( ! [X0,X1] :
        ( ~ v1_partfun1(X1,X0)
        | ~ v4_relat_1(X1,X0)
        | k1_relat_1(X1) = X0
        | ~ v1_relat_1(X1) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f153])).

fof(f222,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f221])).

fof(f226,plain,
    ( spl3_37
    | spl3_38
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f217,f209,f121,f117,f224,f221])).

fof(f117,plain,
    ( spl3_15
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f209,plain,
    ( spl3_35
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_partfun1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f217,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_35 ),
    inference(subsumption_resolution,[],[f216,f118])).

fof(f118,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f117])).

fof(f216,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_16
    | ~ spl3_35 ),
    inference(resolution,[],[f210,f122])).

fof(f210,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_partfun1(sK2,X0) )
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f209])).

fof(f211,plain,
    ( spl3_35
    | ~ spl3_1
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f186,f176,f54,f209])).

fof(f54,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f176,plain,
    ( spl3_29
  <=> ! [X1,X0,X2] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | v1_partfun1(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f186,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_partfun1(sK2,X0) )
    | ~ spl3_1
    | ~ spl3_29 ),
    inference(resolution,[],[f177,f55])).

fof(f55,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f54])).

fof(f177,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(X2,X0,X1)
        | v1_partfun1(X2,X0) )
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f176])).

fof(f203,plain,
    ( ~ spl3_33
    | ~ spl3_16
    | ~ spl3_25
    | spl3_31
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f199,f192,f188,f157,f121,f201])).

fof(f157,plain,
    ( spl3_25
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f188,plain,
    ( spl3_31
  <=> k2_struct_0(sK0) = k10_relat_1(sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f192,plain,
    ( spl3_32
  <=> k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f199,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ spl3_16
    | ~ spl3_25
    | spl3_31
    | ~ spl3_32 ),
    inference(backward_demodulation,[],[f189,f197])).

fof(f197,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2)
    | ~ spl3_16
    | ~ spl3_25
    | ~ spl3_32 ),
    inference(subsumption_resolution,[],[f195,f122])).

fof(f195,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_25
    | ~ spl3_32 ),
    inference(superposition,[],[f193,f158])).

fof(f158,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f157])).

fof(f193,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f192])).

fof(f189,plain,
    ( k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1))
    | spl3_31 ),
    inference(avatar_component_clause,[],[f188])).

fof(f194,plain,
    ( spl3_32
    | ~ spl3_16
    | ~ spl3_28
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f184,f180,f171,f121,f192])).

fof(f171,plain,
    ( spl3_28
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f184,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_16
    | ~ spl3_28
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f183,f181])).

fof(f183,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_16
    | ~ spl3_28 ),
    inference(resolution,[],[f172,f122])).

fof(f172,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f171])).

fof(f190,plain,
    ( ~ spl3_31
    | spl3_18
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f185,f180,f129,f188])).

fof(f185,plain,
    ( k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1))
    | spl3_18
    | ~ spl3_30 ),
    inference(superposition,[],[f130,f181])).

fof(f182,plain,
    ( spl3_30
    | ~ spl3_16
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f174,f163,f121,f180])).

fof(f163,plain,
    ( spl3_26
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f174,plain,
    ( ! [X0] : k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl3_16
    | ~ spl3_26 ),
    inference(resolution,[],[f164,f122])).

fof(f164,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) )
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f163])).

fof(f178,plain,(
    spl3_29 ),
    inference(avatar_split_clause,[],[f41,f176])).

fof(f41,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f173,plain,(
    spl3_28 ),
    inference(avatar_split_clause,[],[f50,f171])).

fof(f50,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).

fof(f165,plain,(
    spl3_26 ),
    inference(avatar_split_clause,[],[f51,f163])).

fof(f51,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f159,plain,(
    spl3_25 ),
    inference(avatar_split_clause,[],[f46,f157])).

fof(f46,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f155,plain,(
    spl3_24 ),
    inference(avatar_split_clause,[],[f45,f153])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).

fof(f147,plain,(
    spl3_22 ),
    inference(avatar_split_clause,[],[f42,f145])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ r1_xboole_0(k2_relat_1(X1),X0)
      | k1_xboole_0 = k10_relat_1(X1,X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) )
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
     => ( k1_xboole_0 = k10_relat_1(X1,X0)
      <=> r1_xboole_0(k2_relat_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).

fof(f135,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f47,f133])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f131,plain,
    ( ~ spl3_18
    | ~ spl3_2
    | ~ spl3_3
    | spl3_9
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f111,f97,f85,f62,f58,f129])).

fof(f58,plain,
    ( spl3_2
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f62,plain,
    ( spl3_3
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f85,plain,
    ( spl3_9
  <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f97,plain,
    ( spl3_12
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f111,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | ~ spl3_2
    | ~ spl3_3
    | spl3_9
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f106,f105])).

fof(f105,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_12 ),
    inference(resolution,[],[f98,f63])).

fof(f63,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f98,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f97])).

fof(f106,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | ~ spl3_2
    | spl3_9
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f86,f104])).

fof(f104,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_2
    | ~ spl3_12 ),
    inference(resolution,[],[f98,f59])).

fof(f59,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f58])).

fof(f86,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_9 ),
    inference(avatar_component_clause,[],[f85])).

fof(f123,plain,
    ( spl3_16
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f110,f97,f77,f62,f58,f121])).

fof(f77,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f110,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f107,f105])).

fof(f107,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f78,f104])).

fof(f78,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f77])).

fof(f119,plain,
    ( spl3_15
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f109,f97,f66,f62,f58,f117])).

fof(f66,plain,
    ( spl3_4
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f109,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f108,f105])).

fof(f108,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f67,f104])).

fof(f67,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f66])).

fof(f103,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f39,f101])).

fof(f39,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( v1_relat_1(X1)
          | ~ m1_subset_1(X1,k1_zfmisc_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f99,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f38,f97])).

fof(f38,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f95,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f37,f93])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f91,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f40,f89])).

fof(f40,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f87,plain,(
    ~ spl3_9 ),
    inference(avatar_split_clause,[],[f33,f85])).

fof(f33,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))
              & ( k1_xboole_0 = k2_struct_0(X0)
                | k1_xboole_0 != k2_struct_0(X1) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( k1_xboole_0 = k2_struct_0(X1)
                   => k1_xboole_0 = k2_struct_0(X0) )
                 => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    inference(negated_conjecture,[],[f13])).

fof(f13,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( k1_xboole_0 = k2_struct_0(X1)
                 => k1_xboole_0 = k2_struct_0(X0) )
               => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).

fof(f83,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f36,f81])).

fof(f36,plain,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] : r1_xboole_0(X0,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

fof(f79,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f32,f77])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f16])).

fof(f75,plain,
    ( spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f29,f73,f70])).

fof(f29,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f68,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f31,f66])).

fof(f31,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f16])).

fof(f64,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f35,f62])).

fof(f35,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f16])).

fof(f60,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f34,f58])).

fof(f34,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f16])).

fof(f56,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f30,f54])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 18:43:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.46  % (20262)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.21/0.46  % (20255)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.46  % (20247)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.46  % (20251)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.46  % (20255)Refutation found. Thanks to Tanya!
% 0.21/0.46  % SZS status Theorem for theBenchmark
% 0.21/0.46  % SZS output start Proof for theBenchmark
% 0.21/0.46  fof(f327,plain,(
% 0.21/0.46    $false),
% 0.21/0.46    inference(avatar_sat_refutation,[],[f56,f60,f64,f68,f75,f79,f83,f87,f91,f95,f99,f103,f119,f123,f131,f135,f147,f155,f159,f165,f173,f178,f182,f190,f194,f203,f211,f226,f235,f238,f241,f288,f304,f306,f318,f326])).
% 0.21/0.46  fof(f326,plain,(
% 0.21/0.46    ~spl3_39 | ~spl3_8 | ~spl3_22 | spl3_51),
% 0.21/0.46    inference(avatar_split_clause,[],[f321,f316,f145,f81,f230])).
% 0.21/0.46  fof(f230,plain,(
% 0.21/0.46    spl3_39 <=> v1_relat_1(sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.21/0.46  fof(f81,plain,(
% 0.21/0.46    spl3_8 <=> ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.46  fof(f145,plain,(
% 0.21/0.46    spl3_22 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.46  fof(f316,plain,(
% 0.21/0.46    spl3_51 <=> k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 0.21/0.46  fof(f321,plain,(
% 0.21/0.46    ~v1_relat_1(sK2) | (~spl3_8 | ~spl3_22 | spl3_51)),
% 0.21/0.46    inference(subsumption_resolution,[],[f320,f82])).
% 0.21/0.46  fof(f82,plain,(
% 0.21/0.46    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) ) | ~spl3_8),
% 0.21/0.46    inference(avatar_component_clause,[],[f81])).
% 0.21/0.46  fof(f320,plain,(
% 0.21/0.46    ~r1_xboole_0(k2_relat_1(sK2),k1_xboole_0) | ~v1_relat_1(sK2) | (~spl3_22 | spl3_51)),
% 0.21/0.46    inference(trivial_inequality_removal,[],[f319])).
% 0.21/0.46  fof(f319,plain,(
% 0.21/0.46    k1_xboole_0 != k1_xboole_0 | ~r1_xboole_0(k2_relat_1(sK2),k1_xboole_0) | ~v1_relat_1(sK2) | (~spl3_22 | spl3_51)),
% 0.21/0.46    inference(superposition,[],[f317,f146])).
% 0.21/0.46  fof(f146,plain,(
% 0.21/0.46    ( ! [X0,X1] : (k1_xboole_0 = k10_relat_1(X1,X0) | ~r1_xboole_0(k2_relat_1(X1),X0) | ~v1_relat_1(X1)) ) | ~spl3_22),
% 0.21/0.46    inference(avatar_component_clause,[],[f145])).
% 0.21/0.46  fof(f317,plain,(
% 0.21/0.46    k1_xboole_0 != k10_relat_1(sK2,k1_xboole_0) | spl3_51),
% 0.21/0.46    inference(avatar_component_clause,[],[f316])).
% 0.21/0.46  fof(f318,plain,(
% 0.21/0.46    ~spl3_51 | spl3_45 | ~spl3_49),
% 0.21/0.46    inference(avatar_split_clause,[],[f307,f302,f286,f316])).
% 0.21/0.46  fof(f286,plain,(
% 0.21/0.46    spl3_45 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.21/0.46  fof(f302,plain,(
% 0.21/0.46    spl3_49 <=> ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.21/0.46  fof(f307,plain,(
% 0.21/0.46    k1_xboole_0 != k10_relat_1(sK2,k1_xboole_0) | (spl3_45 | ~spl3_49)),
% 0.21/0.46    inference(superposition,[],[f287,f303])).
% 0.21/0.46  fof(f303,plain,(
% 0.21/0.46    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,X0)) ) | ~spl3_49),
% 0.21/0.46    inference(avatar_component_clause,[],[f302])).
% 0.21/0.46  fof(f287,plain,(
% 0.21/0.46    k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) | spl3_45),
% 0.21/0.46    inference(avatar_component_clause,[],[f286])).
% 0.21/0.46  fof(f306,plain,(
% 0.21/0.46    spl3_6 | ~spl3_11 | ~spl3_38),
% 0.21/0.46    inference(avatar_split_clause,[],[f243,f224,f93,f73])).
% 0.21/0.46  fof(f73,plain,(
% 0.21/0.46    spl3_6 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.46  fof(f93,plain,(
% 0.21/0.46    spl3_11 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.46  fof(f224,plain,(
% 0.21/0.46    spl3_38 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.21/0.46  fof(f243,plain,(
% 0.21/0.46    k1_xboole_0 = k2_struct_0(sK1) | (~spl3_11 | ~spl3_38)),
% 0.21/0.46    inference(resolution,[],[f225,f94])).
% 0.21/0.46  fof(f94,plain,(
% 0.21/0.46    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl3_11),
% 0.21/0.46    inference(avatar_component_clause,[],[f93])).
% 0.21/0.46  fof(f225,plain,(
% 0.21/0.46    v1_xboole_0(k2_struct_0(sK1)) | ~spl3_38),
% 0.21/0.46    inference(avatar_component_clause,[],[f224])).
% 0.21/0.46  fof(f304,plain,(
% 0.21/0.46    spl3_49 | ~spl3_5 | ~spl3_11 | ~spl3_30 | ~spl3_38),
% 0.21/0.46    inference(avatar_split_clause,[],[f262,f224,f180,f93,f70,f302])).
% 0.21/0.46  fof(f70,plain,(
% 0.21/0.46    spl3_5 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.46  fof(f180,plain,(
% 0.21/0.46    spl3_30 <=> ! [X0] : k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.46  fof(f262,plain,(
% 0.21/0.46    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,X0)) ) | (~spl3_5 | ~spl3_11 | ~spl3_30 | ~spl3_38)),
% 0.21/0.46    inference(backward_demodulation,[],[f251,f71])).
% 0.21/0.46  fof(f71,plain,(
% 0.21/0.46    k1_xboole_0 = k2_struct_0(sK0) | ~spl3_5),
% 0.21/0.46    inference(avatar_component_clause,[],[f70])).
% 0.21/0.46  fof(f251,plain,(
% 0.21/0.46    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2,X0)) ) | (~spl3_11 | ~spl3_30 | ~spl3_38)),
% 0.21/0.46    inference(backward_demodulation,[],[f181,f243])).
% 0.21/0.46  fof(f181,plain,(
% 0.21/0.46    ( ! [X0] : (k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)) ) | ~spl3_30),
% 0.21/0.46    inference(avatar_component_clause,[],[f180])).
% 0.21/0.46  fof(f288,plain,(
% 0.21/0.46    ~spl3_45 | ~spl3_5 | ~spl3_11 | spl3_18 | ~spl3_38),
% 0.21/0.46    inference(avatar_split_clause,[],[f261,f224,f129,f93,f70,f286])).
% 0.21/0.46  fof(f129,plain,(
% 0.21/0.46    spl3_18 <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.46  fof(f261,plain,(
% 0.21/0.46    k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) | (~spl3_5 | ~spl3_11 | spl3_18 | ~spl3_38)),
% 0.21/0.46    inference(backward_demodulation,[],[f250,f71])).
% 0.21/0.46  fof(f250,plain,(
% 0.21/0.46    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2,k1_xboole_0) | (~spl3_11 | spl3_18 | ~spl3_38)),
% 0.21/0.46    inference(backward_demodulation,[],[f130,f243])).
% 0.21/0.46  fof(f130,plain,(
% 0.21/0.46    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_18),
% 0.21/0.46    inference(avatar_component_clause,[],[f129])).
% 0.21/0.46  fof(f241,plain,(
% 0.21/0.46    ~spl3_16 | ~spl3_19 | spl3_40),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f239])).
% 0.21/0.46  fof(f239,plain,(
% 0.21/0.46    $false | (~spl3_16 | ~spl3_19 | spl3_40)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f122,f234,f134])).
% 0.21/0.46  fof(f134,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_19),
% 0.21/0.46    inference(avatar_component_clause,[],[f133])).
% 0.21/0.46  fof(f133,plain,(
% 0.21/0.46    spl3_19 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.46  fof(f234,plain,(
% 0.21/0.46    ~v4_relat_1(sK2,k2_struct_0(sK0)) | spl3_40),
% 0.21/0.46    inference(avatar_component_clause,[],[f233])).
% 0.21/0.46  fof(f233,plain,(
% 0.21/0.46    spl3_40 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.21/0.46  fof(f122,plain,(
% 0.21/0.46    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_16),
% 0.21/0.46    inference(avatar_component_clause,[],[f121])).
% 0.21/0.46  fof(f121,plain,(
% 0.21/0.46    spl3_16 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.46  fof(f238,plain,(
% 0.21/0.46    ~spl3_10 | ~spl3_13 | ~spl3_16 | spl3_39),
% 0.21/0.46    inference(avatar_contradiction_clause,[],[f236])).
% 0.21/0.46  fof(f236,plain,(
% 0.21/0.46    $false | (~spl3_10 | ~spl3_13 | ~spl3_16 | spl3_39)),
% 0.21/0.46    inference(unit_resulting_resolution,[],[f90,f122,f231,f102])).
% 0.21/0.46  fof(f102,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | ~spl3_13),
% 0.21/0.46    inference(avatar_component_clause,[],[f101])).
% 0.21/0.46  fof(f101,plain,(
% 0.21/0.46    spl3_13 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.46  fof(f231,plain,(
% 0.21/0.46    ~v1_relat_1(sK2) | spl3_39),
% 0.21/0.46    inference(avatar_component_clause,[],[f230])).
% 0.21/0.46  fof(f90,plain,(
% 0.21/0.46    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl3_10),
% 0.21/0.46    inference(avatar_component_clause,[],[f89])).
% 0.21/0.46  fof(f89,plain,(
% 0.21/0.46    spl3_10 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.46  fof(f235,plain,(
% 0.21/0.46    ~spl3_39 | ~spl3_40 | ~spl3_24 | spl3_33 | ~spl3_37),
% 0.21/0.46    inference(avatar_split_clause,[],[f228,f221,f201,f153,f233,f230])).
% 0.21/0.46  fof(f153,plain,(
% 0.21/0.46    spl3_24 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.46  fof(f201,plain,(
% 0.21/0.46    spl3_33 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.46  fof(f221,plain,(
% 0.21/0.46    spl3_37 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.21/0.46  fof(f228,plain,(
% 0.21/0.46    ~v4_relat_1(sK2,k2_struct_0(sK0)) | ~v1_relat_1(sK2) | (~spl3_24 | spl3_33 | ~spl3_37)),
% 0.21/0.46    inference(subsumption_resolution,[],[f227,f202])).
% 0.21/0.46  fof(f202,plain,(
% 0.21/0.46    k2_struct_0(sK0) != k1_relat_1(sK2) | spl3_33),
% 0.21/0.46    inference(avatar_component_clause,[],[f201])).
% 0.21/0.46  fof(f227,plain,(
% 0.21/0.46    ~v4_relat_1(sK2,k2_struct_0(sK0)) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl3_24 | ~spl3_37)),
% 0.21/0.46    inference(resolution,[],[f222,f154])).
% 0.21/0.46  fof(f154,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) ) | ~spl3_24),
% 0.21/0.46    inference(avatar_component_clause,[],[f153])).
% 0.21/0.46  fof(f222,plain,(
% 0.21/0.46    v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_37),
% 0.21/0.46    inference(avatar_component_clause,[],[f221])).
% 0.21/0.46  fof(f226,plain,(
% 0.21/0.46    spl3_37 | spl3_38 | ~spl3_15 | ~spl3_16 | ~spl3_35),
% 0.21/0.46    inference(avatar_split_clause,[],[f217,f209,f121,f117,f224,f221])).
% 0.21/0.46  fof(f117,plain,(
% 0.21/0.46    spl3_15 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.46  fof(f209,plain,(
% 0.21/0.46    spl3_35 <=> ! [X1,X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(sK2,X0,X1) | v1_partfun1(sK2,X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.21/0.46  fof(f217,plain,(
% 0.21/0.46    v1_xboole_0(k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_15 | ~spl3_16 | ~spl3_35)),
% 0.21/0.46    inference(subsumption_resolution,[],[f216,f118])).
% 0.21/0.46  fof(f118,plain,(
% 0.21/0.46    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_15),
% 0.21/0.46    inference(avatar_component_clause,[],[f117])).
% 0.21/0.46  fof(f216,plain,(
% 0.21/0.46    v1_xboole_0(k2_struct_0(sK1)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_16 | ~spl3_35)),
% 0.21/0.46    inference(resolution,[],[f210,f122])).
% 0.21/0.46  fof(f210,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(sK2,X0,X1) | v1_partfun1(sK2,X0)) ) | ~spl3_35),
% 0.21/0.46    inference(avatar_component_clause,[],[f209])).
% 0.21/0.46  fof(f211,plain,(
% 0.21/0.46    spl3_35 | ~spl3_1 | ~spl3_29),
% 0.21/0.46    inference(avatar_split_clause,[],[f186,f176,f54,f209])).
% 0.21/0.46  fof(f54,plain,(
% 0.21/0.46    spl3_1 <=> v1_funct_1(sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.46  fof(f176,plain,(
% 0.21/0.46    spl3_29 <=> ! [X1,X0,X2] : (v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.46  fof(f186,plain,(
% 0.21/0.46    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(sK2,X0,X1) | v1_partfun1(sK2,X0)) ) | (~spl3_1 | ~spl3_29)),
% 0.21/0.46    inference(resolution,[],[f177,f55])).
% 0.21/0.46  fof(f55,plain,(
% 0.21/0.46    v1_funct_1(sK2) | ~spl3_1),
% 0.21/0.46    inference(avatar_component_clause,[],[f54])).
% 0.21/0.46  fof(f177,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) ) | ~spl3_29),
% 0.21/0.46    inference(avatar_component_clause,[],[f176])).
% 0.21/0.46  fof(f203,plain,(
% 0.21/0.46    ~spl3_33 | ~spl3_16 | ~spl3_25 | spl3_31 | ~spl3_32),
% 0.21/0.46    inference(avatar_split_clause,[],[f199,f192,f188,f157,f121,f201])).
% 0.21/0.46  fof(f157,plain,(
% 0.21/0.46    spl3_25 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.46  fof(f188,plain,(
% 0.21/0.46    spl3_31 <=> k2_struct_0(sK0) = k10_relat_1(sK2,k2_struct_0(sK1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.46  fof(f192,plain,(
% 0.21/0.46    spl3_32 <=> k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.46  fof(f199,plain,(
% 0.21/0.46    k2_struct_0(sK0) != k1_relat_1(sK2) | (~spl3_16 | ~spl3_25 | spl3_31 | ~spl3_32)),
% 0.21/0.46    inference(backward_demodulation,[],[f189,f197])).
% 0.21/0.46  fof(f197,plain,(
% 0.21/0.46    k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2) | (~spl3_16 | ~spl3_25 | ~spl3_32)),
% 0.21/0.46    inference(subsumption_resolution,[],[f195,f122])).
% 0.21/0.46  fof(f195,plain,(
% 0.21/0.46    k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_25 | ~spl3_32)),
% 0.21/0.46    inference(superposition,[],[f193,f158])).
% 0.21/0.46  fof(f158,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_25),
% 0.21/0.46    inference(avatar_component_clause,[],[f157])).
% 0.21/0.46  fof(f193,plain,(
% 0.21/0.46    k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_32),
% 0.21/0.46    inference(avatar_component_clause,[],[f192])).
% 0.21/0.46  fof(f189,plain,(
% 0.21/0.46    k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1)) | spl3_31),
% 0.21/0.46    inference(avatar_component_clause,[],[f188])).
% 0.21/0.46  fof(f194,plain,(
% 0.21/0.46    spl3_32 | ~spl3_16 | ~spl3_28 | ~spl3_30),
% 0.21/0.46    inference(avatar_split_clause,[],[f184,f180,f171,f121,f192])).
% 0.21/0.46  fof(f171,plain,(
% 0.21/0.46    spl3_28 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.46  fof(f184,plain,(
% 0.21/0.46    k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_16 | ~spl3_28 | ~spl3_30)),
% 0.21/0.46    inference(forward_demodulation,[],[f183,f181])).
% 0.21/0.46  fof(f183,plain,(
% 0.21/0.46    k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_16 | ~spl3_28)),
% 0.21/0.46    inference(resolution,[],[f172,f122])).
% 0.21/0.46  fof(f172,plain,(
% 0.21/0.46    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)) ) | ~spl3_28),
% 0.21/0.46    inference(avatar_component_clause,[],[f171])).
% 0.21/0.46  fof(f190,plain,(
% 0.21/0.46    ~spl3_31 | spl3_18 | ~spl3_30),
% 0.21/0.46    inference(avatar_split_clause,[],[f185,f180,f129,f188])).
% 0.21/0.46  fof(f185,plain,(
% 0.21/0.46    k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1)) | (spl3_18 | ~spl3_30)),
% 0.21/0.46    inference(superposition,[],[f130,f181])).
% 0.21/0.46  fof(f182,plain,(
% 0.21/0.46    spl3_30 | ~spl3_16 | ~spl3_26),
% 0.21/0.46    inference(avatar_split_clause,[],[f174,f163,f121,f180])).
% 0.21/0.46  fof(f163,plain,(
% 0.21/0.46    spl3_26 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.46    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.46  fof(f174,plain,(
% 0.21/0.47    ( ! [X0] : (k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)) ) | (~spl3_16 | ~spl3_26)),
% 0.21/0.47    inference(resolution,[],[f164,f122])).
% 0.21/0.47  fof(f164,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) ) | ~spl3_26),
% 0.21/0.47    inference(avatar_component_clause,[],[f163])).
% 0.21/0.47  fof(f178,plain,(
% 0.21/0.47    spl3_29),
% 0.21/0.47    inference(avatar_split_clause,[],[f41,f176])).
% 0.21/0.47  fof(f41,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f21])).
% 0.21/0.47  fof(f21,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.47    inference(flattening,[],[f20])).
% 0.21/0.47  fof(f20,plain,(
% 0.21/0.47    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f10])).
% 0.21/0.47  fof(f10,axiom,(
% 0.21/0.47    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.47  fof(f173,plain,(
% 0.21/0.47    spl3_28),
% 0.21/0.47    inference(avatar_split_clause,[],[f50,f171])).
% 0.21/0.47  fof(f50,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f27])).
% 0.21/0.47  fof(f27,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f9])).
% 0.21/0.47  fof(f9,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_relset_1)).
% 0.21/0.47  fof(f165,plain,(
% 0.21/0.47    spl3_26),
% 0.21/0.47    inference(avatar_split_clause,[],[f51,f163])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f28])).
% 0.21/0.47  fof(f28,plain,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f8])).
% 0.21/0.47  fof(f8,axiom,(
% 0.21/0.47    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.47  fof(f159,plain,(
% 0.21/0.47    spl3_25),
% 0.21/0.47    inference(avatar_split_clause,[],[f46,f157])).
% 0.21/0.47  fof(f46,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f25])).
% 0.21/0.47  fof(f25,plain,(
% 0.21/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f7])).
% 0.21/0.47  fof(f7,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.47  fof(f155,plain,(
% 0.21/0.47    spl3_24),
% 0.21/0.47    inference(avatar_split_clause,[],[f45,f153])).
% 0.21/0.47  fof(f45,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f24])).
% 0.21/0.47  fof(f24,plain,(
% 0.21/0.47    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(flattening,[],[f23])).
% 0.21/0.47  fof(f23,plain,(
% 0.21/0.47    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.47    inference(ennf_transformation,[],[f11])).
% 0.21/0.47  fof(f11,axiom,(
% 0.21/0.47    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.47  fof(f147,plain,(
% 0.21/0.47    spl3_22),
% 0.21/0.47    inference(avatar_split_clause,[],[f42,f145])).
% 0.21/0.47  fof(f42,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X1) | ~r1_xboole_0(k2_relat_1(X1),X0) | k1_xboole_0 = k10_relat_1(X1,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f22])).
% 0.21/0.47  fof(f22,plain,(
% 0.21/0.47    ! [X0,X1] : ((k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)) | ~v1_relat_1(X1))),
% 0.21/0.47    inference(ennf_transformation,[],[f5])).
% 0.21/0.47  fof(f5,axiom,(
% 0.21/0.47    ! [X0,X1] : (v1_relat_1(X1) => (k1_xboole_0 = k10_relat_1(X1,X0) <=> r1_xboole_0(k2_relat_1(X1),X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t173_relat_1)).
% 0.21/0.47  fof(f135,plain,(
% 0.21/0.47    spl3_19),
% 0.21/0.47    inference(avatar_split_clause,[],[f47,f133])).
% 0.21/0.47  fof(f47,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f26])).
% 0.21/0.47  fof(f26,plain,(
% 0.21/0.47    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.47    inference(ennf_transformation,[],[f6])).
% 0.21/0.47  fof(f6,axiom,(
% 0.21/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    ~spl3_18 | ~spl3_2 | ~spl3_3 | spl3_9 | ~spl3_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f111,f97,f85,f62,f58,f129])).
% 0.21/0.47  fof(f58,plain,(
% 0.21/0.47    spl3_2 <=> l1_struct_0(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.47  fof(f62,plain,(
% 0.21/0.47    spl3_3 <=> l1_struct_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.47  fof(f85,plain,(
% 0.21/0.47    spl3_9 <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.47  fof(f97,plain,(
% 0.21/0.47    spl3_12 <=> ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (~spl3_2 | ~spl3_3 | spl3_9 | ~spl3_12)),
% 0.21/0.47    inference(backward_demodulation,[],[f106,f105])).
% 0.21/0.47  fof(f105,plain,(
% 0.21/0.47    k2_struct_0(sK0) = u1_struct_0(sK0) | (~spl3_3 | ~spl3_12)),
% 0.21/0.47    inference(resolution,[],[f98,f63])).
% 0.21/0.47  fof(f63,plain,(
% 0.21/0.47    l1_struct_0(sK0) | ~spl3_3),
% 0.21/0.47    inference(avatar_component_clause,[],[f62])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl3_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f97])).
% 0.21/0.47  fof(f106,plain,(
% 0.21/0.47    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (~spl3_2 | spl3_9 | ~spl3_12)),
% 0.21/0.47    inference(backward_demodulation,[],[f86,f104])).
% 0.21/0.47  fof(f104,plain,(
% 0.21/0.47    k2_struct_0(sK1) = u1_struct_0(sK1) | (~spl3_2 | ~spl3_12)),
% 0.21/0.47    inference(resolution,[],[f98,f59])).
% 0.21/0.47  fof(f59,plain,(
% 0.21/0.47    l1_struct_0(sK1) | ~spl3_2),
% 0.21/0.47    inference(avatar_component_clause,[],[f58])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f85])).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    spl3_16 | ~spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f110,f97,f77,f62,f58,f121])).
% 0.21/0.47  fof(f77,plain,(
% 0.21/0.47    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_12)),
% 0.21/0.47    inference(backward_demodulation,[],[f107,f105])).
% 0.21/0.47  fof(f107,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_2 | ~spl3_7 | ~spl3_12)),
% 0.21/0.47    inference(backward_demodulation,[],[f78,f104])).
% 0.21/0.47  fof(f78,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_7),
% 0.21/0.47    inference(avatar_component_clause,[],[f77])).
% 0.21/0.47  fof(f119,plain,(
% 0.21/0.47    spl3_15 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f109,f97,f66,f62,f58,f117])).
% 0.21/0.47  fof(f66,plain,(
% 0.21/0.47    spl3_4 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.47  fof(f109,plain,(
% 0.21/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_12)),
% 0.21/0.47    inference(backward_demodulation,[],[f108,f105])).
% 0.21/0.47  fof(f108,plain,(
% 0.21/0.47    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_2 | ~spl3_4 | ~spl3_12)),
% 0.21/0.47    inference(backward_demodulation,[],[f67,f104])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_4),
% 0.21/0.47    inference(avatar_component_clause,[],[f66])).
% 0.21/0.47  fof(f103,plain,(
% 0.21/0.47    spl3_13),
% 0.21/0.47    inference(avatar_split_clause,[],[f39,f101])).
% 0.21/0.47  fof(f39,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f19])).
% 0.21/0.47  fof(f19,plain,(
% 0.21/0.47    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f3])).
% 0.21/0.47  fof(f3,axiom,(
% 0.21/0.47    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    spl3_12),
% 0.21/0.47    inference(avatar_split_clause,[],[f38,f97])).
% 0.21/0.47  fof(f38,plain,(
% 0.21/0.47    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f18])).
% 0.21/0.47  fof(f18,plain,(
% 0.21/0.47    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f12])).
% 0.21/0.47  fof(f12,axiom,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    spl3_11),
% 0.21/0.47    inference(avatar_split_clause,[],[f37,f93])).
% 0.21/0.47  fof(f37,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.47    inference(cnf_transformation,[],[f17])).
% 0.21/0.47  fof(f17,plain,(
% 0.21/0.47    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f1])).
% 0.21/0.47  fof(f1,axiom,(
% 0.21/0.47    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.47  fof(f91,plain,(
% 0.21/0.47    spl3_10),
% 0.21/0.47    inference(avatar_split_clause,[],[f40,f89])).
% 0.21/0.47  fof(f40,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.47    inference(cnf_transformation,[],[f4])).
% 0.21/0.47  fof(f4,axiom,(
% 0.21/0.47    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    ~spl3_9),
% 0.21/0.47    inference(avatar_split_clause,[],[f33,f85])).
% 0.21/0.47  fof(f33,plain,(
% 0.21/0.47    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f16,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.47    inference(flattening,[],[f15])).
% 0.21/0.47  fof(f15,plain,(
% 0.21/0.47    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.47    inference(ennf_transformation,[],[f14])).
% 0.21/0.47  fof(f14,negated_conjecture,(
% 0.21/0.47    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.21/0.47    inference(negated_conjecture,[],[f13])).
% 0.21/0.47  fof(f13,conjecture,(
% 0.21/0.47    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t52_tops_2)).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    spl3_8),
% 0.21/0.47    inference(avatar_split_clause,[],[f36,f81])).
% 0.21/0.47  fof(f36,plain,(
% 0.21/0.47    ( ! [X0] : (r1_xboole_0(X0,k1_xboole_0)) )),
% 0.21/0.47    inference(cnf_transformation,[],[f2])).
% 0.21/0.47  fof(f2,axiom,(
% 0.21/0.47    ! [X0] : r1_xboole_0(X0,k1_xboole_0)),
% 0.21/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).
% 0.21/0.47  fof(f79,plain,(
% 0.21/0.47    spl3_7),
% 0.21/0.47    inference(avatar_split_clause,[],[f32,f77])).
% 0.21/0.47  fof(f32,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f75,plain,(
% 0.21/0.47    spl3_5 | ~spl3_6),
% 0.21/0.47    inference(avatar_split_clause,[],[f29,f73,f70])).
% 0.21/0.47  fof(f29,plain,(
% 0.21/0.47    k1_xboole_0 != k2_struct_0(sK1) | k1_xboole_0 = k2_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    spl3_4),
% 0.21/0.47    inference(avatar_split_clause,[],[f31,f66])).
% 0.21/0.47  fof(f31,plain,(
% 0.21/0.47    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f64,plain,(
% 0.21/0.47    spl3_3),
% 0.21/0.47    inference(avatar_split_clause,[],[f35,f62])).
% 0.21/0.47  fof(f35,plain,(
% 0.21/0.47    l1_struct_0(sK0)),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f60,plain,(
% 0.21/0.47    spl3_2),
% 0.21/0.47    inference(avatar_split_clause,[],[f34,f58])).
% 0.21/0.47  fof(f34,plain,(
% 0.21/0.47    l1_struct_0(sK1)),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  fof(f56,plain,(
% 0.21/0.47    spl3_1),
% 0.21/0.47    inference(avatar_split_clause,[],[f30,f54])).
% 0.21/0.47  fof(f30,plain,(
% 0.21/0.47    v1_funct_1(sK2)),
% 0.21/0.47    inference(cnf_transformation,[],[f16])).
% 0.21/0.47  % SZS output end Proof for theBenchmark
% 0.21/0.47  % (20255)------------------------------
% 0.21/0.47  % (20255)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (20255)Termination reason: Refutation
% 0.21/0.47  
% 0.21/0.47  % (20255)Memory used [KB]: 10746
% 0.21/0.47  % (20255)Time elapsed: 0.061 s
% 0.21/0.47  % (20255)------------------------------
% 0.21/0.47  % (20255)------------------------------
% 0.21/0.47  % (20247)Refutation not found, incomplete strategy% (20247)------------------------------
% 0.21/0.47  % (20247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (20247)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.47  
% 0.21/0.47  % (20245)Success in time 0.114 s
%------------------------------------------------------------------------------
