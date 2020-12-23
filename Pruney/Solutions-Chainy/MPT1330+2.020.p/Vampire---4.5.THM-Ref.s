%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:13:57 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  178 ( 332 expanded)
%              Number of leaves         :   46 ( 154 expanded)
%              Depth                    :    6
%              Number of atoms          :  522 (1033 expanded)
%              Number of equality atoms :   93 ( 236 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f311,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f72,f76,f80,f84,f88,f92,f96,f100,f112,f116,f124,f132,f144,f148,f154,f162,f167,f171,f178,f183,f192,f200,f213,f222,f225,f228,f273,f287,f291,f296,f310])).

fof(f310,plain,
    ( ~ spl3_37
    | ~ spl3_12
    | spl3_48 ),
    inference(avatar_split_clause,[],[f305,f294,f94,f217])).

fof(f217,plain,
    ( spl3_37
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f94,plain,
    ( spl3_12
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f294,plain,
    ( spl3_48
  <=> k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f305,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_12
    | spl3_48 ),
    inference(trivial_inequality_removal,[],[f304])).

fof(f304,plain,
    ( k1_xboole_0 != k1_xboole_0
    | ~ v1_relat_1(sK2)
    | ~ spl3_12
    | spl3_48 ),
    inference(superposition,[],[f295,f95])).

fof(f95,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f94])).

fof(f295,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,k1_xboole_0)
    | spl3_48 ),
    inference(avatar_component_clause,[],[f294])).

fof(f296,plain,
    ( ~ spl3_48
    | spl3_43
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f292,f289,f271,f294])).

fof(f271,plain,
    ( spl3_43
  <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f289,plain,
    ( spl3_47
  <=> ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f292,plain,
    ( k1_xboole_0 != k10_relat_1(sK2,k1_xboole_0)
    | spl3_43
    | ~ spl3_47 ),
    inference(superposition,[],[f272,f290])).

fof(f290,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,X0)
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f289])).

fof(f272,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)
    | spl3_43 ),
    inference(avatar_component_clause,[],[f271])).

fof(f291,plain,
    ( spl3_47
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_27
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f247,f211,f165,f86,f67,f289])).

fof(f67,plain,
    ( spl3_5
  <=> k1_xboole_0 = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f86,plain,
    ( spl3_10
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f165,plain,
    ( spl3_27
  <=> ! [X0] : k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f211,plain,
    ( spl3_36
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f247,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,X0)
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_27
    | ~ spl3_36 ),
    inference(backward_demodulation,[],[f238,f68])).

fof(f68,plain,
    ( k1_xboole_0 = k2_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f67])).

fof(f238,plain,
    ( ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2,X0)
    | ~ spl3_10
    | ~ spl3_27
    | ~ spl3_36 ),
    inference(backward_demodulation,[],[f166,f230])).

fof(f230,plain,
    ( k1_xboole_0 = k2_struct_0(sK1)
    | ~ spl3_10
    | ~ spl3_36 ),
    inference(resolution,[],[f212,f87])).

fof(f87,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f86])).

fof(f212,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f211])).

fof(f166,plain,
    ( ! [X0] : k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f165])).

fof(f287,plain,
    ( spl3_6
    | ~ spl3_10
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f230,f211,f86,f70])).

fof(f70,plain,
    ( spl3_6
  <=> k1_xboole_0 = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f273,plain,
    ( ~ spl3_43
    | ~ spl3_5
    | ~ spl3_10
    | spl3_17
    | ~ spl3_36 ),
    inference(avatar_split_clause,[],[f246,f211,f122,f86,f67,f271])).

fof(f122,plain,
    ( spl3_17
  <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f246,plain,
    ( k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl3_5
    | ~ spl3_10
    | spl3_17
    | ~ spl3_36 ),
    inference(backward_demodulation,[],[f237,f68])).

fof(f237,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2,k1_xboole_0)
    | ~ spl3_10
    | spl3_17
    | ~ spl3_36 ),
    inference(backward_demodulation,[],[f123,f230])).

fof(f123,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f122])).

fof(f228,plain,
    ( ~ spl3_15
    | ~ spl3_19
    | spl3_38 ),
    inference(avatar_contradiction_clause,[],[f226])).

fof(f226,plain,
    ( $false
    | ~ spl3_15
    | ~ spl3_19
    | spl3_38 ),
    inference(unit_resulting_resolution,[],[f115,f221,f131])).

fof(f131,plain,
    ( ! [X2,X0,X1] :
        ( v4_relat_1(X2,X0)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f130])).

fof(f130,plain,
    ( spl3_19
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v4_relat_1(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f221,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | spl3_38 ),
    inference(avatar_component_clause,[],[f220])).

fof(f220,plain,
    ( spl3_38
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f115,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f114])).

fof(f114,plain,
    ( spl3_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f225,plain,
    ( ~ spl3_9
    | ~ spl3_13
    | ~ spl3_15
    | spl3_37 ),
    inference(avatar_contradiction_clause,[],[f223])).

fof(f223,plain,
    ( $false
    | ~ spl3_9
    | ~ spl3_13
    | ~ spl3_15
    | spl3_37 ),
    inference(unit_resulting_resolution,[],[f83,f115,f218,f99])).

fof(f99,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f218,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_37 ),
    inference(avatar_component_clause,[],[f217])).

fof(f83,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f82])).

fof(f82,plain,
    ( spl3_9
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f222,plain,
    ( ~ spl3_37
    | ~ spl3_38
    | ~ spl3_22
    | spl3_31
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f215,f208,f190,f142,f220,f217])).

fof(f142,plain,
    ( spl3_22
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X1)
        | ~ v4_relat_1(X1,X0)
        | k1_relat_1(X1) = X0
        | ~ v1_partfun1(X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f190,plain,
    ( spl3_31
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f208,plain,
    ( spl3_35
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f215,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl3_22
    | spl3_31
    | ~ spl3_35 ),
    inference(subsumption_resolution,[],[f214,f191])).

fof(f191,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | spl3_31 ),
    inference(avatar_component_clause,[],[f190])).

fof(f214,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_22
    | ~ spl3_35 ),
    inference(resolution,[],[f209,f143])).

fof(f143,plain,
    ( ! [X0,X1] :
        ( ~ v1_partfun1(X1,X0)
        | ~ v4_relat_1(X1,X0)
        | k1_relat_1(X1) = X0
        | ~ v1_relat_1(X1) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f142])).

fof(f209,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f208])).

fof(f213,plain,
    ( spl3_35
    | spl3_36
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f206,f198,f114,f110,f211,f208])).

fof(f110,plain,
    ( spl3_14
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f198,plain,
    ( spl3_33
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_partfun1(sK2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f206,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_14
    | ~ spl3_15
    | ~ spl3_33 ),
    inference(subsumption_resolution,[],[f205,f111])).

fof(f111,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f110])).

fof(f205,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_15
    | ~ spl3_33 ),
    inference(resolution,[],[f199,f115])).

fof(f199,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_partfun1(sK2,X0) )
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f198])).

fof(f200,plain,
    ( spl3_33
    | ~ spl3_1
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f179,f169,f51,f198])).

fof(f51,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f169,plain,
    ( spl3_28
  <=> ! [X1,X0,X2] :
        ( v1_xboole_0(X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | v1_partfun1(X2,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f179,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_partfun1(sK2,X0) )
    | ~ spl3_1
    | ~ spl3_28 ),
    inference(resolution,[],[f170,f52])).

fof(f52,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f51])).

fof(f170,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1)
        | ~ v1_funct_2(X2,X0,X1)
        | v1_partfun1(X2,X0) )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f169])).

fof(f192,plain,
    ( ~ spl3_31
    | ~ spl3_15
    | ~ spl3_23
    | spl3_29
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f188,f181,f176,f146,f114,f190])).

fof(f146,plain,
    ( spl3_23
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f176,plain,
    ( spl3_29
  <=> k2_struct_0(sK0) = k10_relat_1(sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f181,plain,
    ( spl3_30
  <=> k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f188,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | ~ spl3_15
    | ~ spl3_23
    | spl3_29
    | ~ spl3_30 ),
    inference(backward_demodulation,[],[f177,f186])).

fof(f186,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2)
    | ~ spl3_15
    | ~ spl3_23
    | ~ spl3_30 ),
    inference(subsumption_resolution,[],[f184,f115])).

fof(f184,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_23
    | ~ spl3_30 ),
    inference(superposition,[],[f182,f147])).

fof(f147,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f146])).

fof(f182,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f181])).

fof(f177,plain,
    ( k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1))
    | spl3_29 ),
    inference(avatar_component_clause,[],[f176])).

fof(f183,plain,
    ( spl3_30
    | ~ spl3_15
    | ~ spl3_26
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f174,f165,f160,f114,f181])).

fof(f160,plain,
    ( spl3_26
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f174,plain,
    ( k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_15
    | ~ spl3_26
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f173,f166])).

fof(f173,plain,
    ( k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_15
    | ~ spl3_26 ),
    inference(resolution,[],[f161,f115])).

fof(f161,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) )
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f160])).

fof(f178,plain,
    ( ~ spl3_29
    | spl3_17
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f172,f165,f122,f176])).

fof(f172,plain,
    ( k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1))
    | spl3_17
    | ~ spl3_27 ),
    inference(superposition,[],[f123,f166])).

fof(f171,plain,(
    spl3_28 ),
    inference(avatar_split_clause,[],[f40,f169])).

fof(f40,plain,(
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
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f167,plain,
    ( spl3_27
    | ~ spl3_15
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f163,f152,f114,f165])).

fof(f152,plain,
    ( spl3_24
  <=> ! [X1,X3,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f163,plain,
    ( ! [X0] : k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)
    | ~ spl3_15
    | ~ spl3_24 ),
    inference(resolution,[],[f153,f115])).

fof(f153,plain,
    ( ! [X2,X0,X3,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f152])).

fof(f162,plain,(
    spl3_26 ),
    inference(avatar_split_clause,[],[f47,f160])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)
        & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f154,plain,(
    spl3_24 ),
    inference(avatar_split_clause,[],[f48,f152])).

fof(f48,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f148,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f43,f146])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f144,plain,(
    spl3_22 ),
    inference(avatar_split_clause,[],[f42,f142])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X1)
      | ~ v4_relat_1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_partfun1(X1,X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f132,plain,(
    spl3_19 ),
    inference(avatar_split_clause,[],[f44,f130])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f124,plain,
    ( ~ spl3_17
    | ~ spl3_2
    | ~ spl3_3
    | spl3_8
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f108,f90,f78,f59,f55,f122])).

fof(f55,plain,
    ( spl3_2
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f59,plain,
    ( spl3_3
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f78,plain,
    ( spl3_8
  <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f90,plain,
    ( spl3_11
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f108,plain,
    ( k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | ~ spl3_2
    | ~ spl3_3
    | spl3_8
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f103,f102])).

fof(f102,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_3
    | ~ spl3_11 ),
    inference(resolution,[],[f91,f60])).

fof(f60,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f59])).

fof(f91,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f90])).

fof(f103,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))
    | ~ spl3_2
    | spl3_8
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f79,f101])).

fof(f101,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_2
    | ~ spl3_11 ),
    inference(resolution,[],[f91,f56])).

fof(f56,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f55])).

fof(f79,plain,
    ( k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f78])).

fof(f116,plain,
    ( spl3_15
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f107,f90,f74,f59,f55,f114])).

fof(f74,plain,
    ( spl3_7
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f107,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f104,f102])).

fof(f104,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_2
    | ~ spl3_7
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f75,f101])).

fof(f75,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f74])).

fof(f112,plain,
    ( spl3_14
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f106,f90,f63,f59,f55,f110])).

fof(f63,plain,
    ( spl3_4
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f106,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_2
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f105,f102])).

fof(f105,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_2
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f64,f101])).

fof(f64,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f63])).

fof(f100,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f38,f98])).

fof(f38,plain,(
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
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ! [X1] :
          ( m1_subset_1(X1,k1_zfmisc_1(X0))
         => v1_relat_1(X1) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f96,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f37,f94])).

fof(f37,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).

fof(f92,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f36,f90])).

fof(f36,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f88,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f35,f86])).

fof(f35,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f84,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f39,f82])).

fof(f39,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

% (14240)Refutation not found, incomplete strategy% (14240)------------------------------
% (14240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (14240)Termination reason: Refutation not found, incomplete strategy

% (14240)Memory used [KB]: 10746
% (14240)Time elapsed: 0.068 s
% (14240)------------------------------
% (14240)------------------------------
fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f80,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f32,f78])).

fof(f32,plain,(
    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f15])).

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
    inference(flattening,[],[f14])).

fof(f14,plain,(
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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).

fof(f76,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f31,f74])).

fof(f31,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f72,plain,
    ( spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f28,f70,f67])).

fof(f28,plain,
    ( k1_xboole_0 != k2_struct_0(sK1)
    | k1_xboole_0 = k2_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f65,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f30,f63])).

fof(f30,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f61,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f34,f59])).

fof(f34,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f57,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f33,f55])).

fof(f33,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f53,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f29,f51])).

fof(f29,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 11:10:15 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (14255)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.47  % (14247)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.47  % (14240)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.47  % (14241)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (14247)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % SZS output start Proof for theBenchmark
% 0.21/0.47  fof(f311,plain,(
% 0.21/0.47    $false),
% 0.21/0.47    inference(avatar_sat_refutation,[],[f53,f57,f61,f65,f72,f76,f80,f84,f88,f92,f96,f100,f112,f116,f124,f132,f144,f148,f154,f162,f167,f171,f178,f183,f192,f200,f213,f222,f225,f228,f273,f287,f291,f296,f310])).
% 0.21/0.47  fof(f310,plain,(
% 0.21/0.47    ~spl3_37 | ~spl3_12 | spl3_48),
% 0.21/0.47    inference(avatar_split_clause,[],[f305,f294,f94,f217])).
% 0.21/0.47  fof(f217,plain,(
% 0.21/0.47    spl3_37 <=> v1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.21/0.47  fof(f94,plain,(
% 0.21/0.47    spl3_12 <=> ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.47  fof(f294,plain,(
% 0.21/0.47    spl3_48 <=> k1_xboole_0 = k10_relat_1(sK2,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.21/0.47  fof(f305,plain,(
% 0.21/0.47    ~v1_relat_1(sK2) | (~spl3_12 | spl3_48)),
% 0.21/0.47    inference(trivial_inequality_removal,[],[f304])).
% 0.21/0.47  fof(f304,plain,(
% 0.21/0.47    k1_xboole_0 != k1_xboole_0 | ~v1_relat_1(sK2) | (~spl3_12 | spl3_48)),
% 0.21/0.47    inference(superposition,[],[f295,f95])).
% 0.21/0.47  fof(f95,plain,(
% 0.21/0.47    ( ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0)) ) | ~spl3_12),
% 0.21/0.47    inference(avatar_component_clause,[],[f94])).
% 0.21/0.47  fof(f295,plain,(
% 0.21/0.47    k1_xboole_0 != k10_relat_1(sK2,k1_xboole_0) | spl3_48),
% 0.21/0.47    inference(avatar_component_clause,[],[f294])).
% 0.21/0.47  fof(f296,plain,(
% 0.21/0.47    ~spl3_48 | spl3_43 | ~spl3_47),
% 0.21/0.47    inference(avatar_split_clause,[],[f292,f289,f271,f294])).
% 0.21/0.47  fof(f271,plain,(
% 0.21/0.47    spl3_43 <=> k1_xboole_0 = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.21/0.47  fof(f289,plain,(
% 0.21/0.47    spl3_47 <=> ! [X0] : k10_relat_1(sK2,X0) = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.21/0.47  fof(f292,plain,(
% 0.21/0.47    k1_xboole_0 != k10_relat_1(sK2,k1_xboole_0) | (spl3_43 | ~spl3_47)),
% 0.21/0.47    inference(superposition,[],[f272,f290])).
% 0.21/0.47  fof(f290,plain,(
% 0.21/0.47    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,X0)) ) | ~spl3_47),
% 0.21/0.47    inference(avatar_component_clause,[],[f289])).
% 0.21/0.47  fof(f272,plain,(
% 0.21/0.47    k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) | spl3_43),
% 0.21/0.47    inference(avatar_component_clause,[],[f271])).
% 0.21/0.47  fof(f291,plain,(
% 0.21/0.47    spl3_47 | ~spl3_5 | ~spl3_10 | ~spl3_27 | ~spl3_36),
% 0.21/0.47    inference(avatar_split_clause,[],[f247,f211,f165,f86,f67,f289])).
% 0.21/0.47  fof(f67,plain,(
% 0.21/0.47    spl3_5 <=> k1_xboole_0 = k2_struct_0(sK0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.47  fof(f86,plain,(
% 0.21/0.47    spl3_10 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.47  fof(f165,plain,(
% 0.21/0.47    spl3_27 <=> ! [X0] : k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.47  fof(f211,plain,(
% 0.21/0.47    spl3_36 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.47  fof(f247,plain,(
% 0.21/0.47    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,X0)) ) | (~spl3_5 | ~spl3_10 | ~spl3_27 | ~spl3_36)),
% 0.21/0.47    inference(backward_demodulation,[],[f238,f68])).
% 0.21/0.47  fof(f68,plain,(
% 0.21/0.47    k1_xboole_0 = k2_struct_0(sK0) | ~spl3_5),
% 0.21/0.47    inference(avatar_component_clause,[],[f67])).
% 0.21/0.47  fof(f238,plain,(
% 0.21/0.47    ( ! [X0] : (k10_relat_1(sK2,X0) = k8_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2,X0)) ) | (~spl3_10 | ~spl3_27 | ~spl3_36)),
% 0.21/0.47    inference(backward_demodulation,[],[f166,f230])).
% 0.21/0.47  fof(f230,plain,(
% 0.21/0.47    k1_xboole_0 = k2_struct_0(sK1) | (~spl3_10 | ~spl3_36)),
% 0.21/0.47    inference(resolution,[],[f212,f87])).
% 0.21/0.47  fof(f87,plain,(
% 0.21/0.47    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl3_10),
% 0.21/0.47    inference(avatar_component_clause,[],[f86])).
% 0.21/0.47  fof(f212,plain,(
% 0.21/0.47    v1_xboole_0(k2_struct_0(sK1)) | ~spl3_36),
% 0.21/0.47    inference(avatar_component_clause,[],[f211])).
% 0.21/0.47  fof(f166,plain,(
% 0.21/0.47    ( ! [X0] : (k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)) ) | ~spl3_27),
% 0.21/0.47    inference(avatar_component_clause,[],[f165])).
% 0.21/0.47  fof(f287,plain,(
% 0.21/0.47    spl3_6 | ~spl3_10 | ~spl3_36),
% 0.21/0.47    inference(avatar_split_clause,[],[f230,f211,f86,f70])).
% 0.21/0.47  fof(f70,plain,(
% 0.21/0.47    spl3_6 <=> k1_xboole_0 = k2_struct_0(sK1)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.47  fof(f273,plain,(
% 0.21/0.47    ~spl3_43 | ~spl3_5 | ~spl3_10 | spl3_17 | ~spl3_36),
% 0.21/0.47    inference(avatar_split_clause,[],[f246,f211,f122,f86,f67,f271])).
% 0.21/0.47  fof(f122,plain,(
% 0.21/0.47    spl3_17 <=> k2_struct_0(sK0) = k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.47  fof(f246,plain,(
% 0.21/0.47    k1_xboole_0 != k8_relset_1(k1_xboole_0,k1_xboole_0,sK2,k1_xboole_0) | (~spl3_5 | ~spl3_10 | spl3_17 | ~spl3_36)),
% 0.21/0.47    inference(backward_demodulation,[],[f237,f68])).
% 0.21/0.47  fof(f237,plain,(
% 0.21/0.47    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k1_xboole_0,sK2,k1_xboole_0) | (~spl3_10 | spl3_17 | ~spl3_36)),
% 0.21/0.47    inference(backward_demodulation,[],[f123,f230])).
% 0.21/0.47  fof(f123,plain,(
% 0.21/0.47    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_17),
% 0.21/0.47    inference(avatar_component_clause,[],[f122])).
% 0.21/0.47  fof(f228,plain,(
% 0.21/0.47    ~spl3_15 | ~spl3_19 | spl3_38),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f226])).
% 0.21/0.47  fof(f226,plain,(
% 0.21/0.47    $false | (~spl3_15 | ~spl3_19 | spl3_38)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f115,f221,f131])).
% 0.21/0.47  fof(f131,plain,(
% 0.21/0.47    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_19),
% 0.21/0.47    inference(avatar_component_clause,[],[f130])).
% 0.21/0.47  fof(f130,plain,(
% 0.21/0.47    spl3_19 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.47  fof(f221,plain,(
% 0.21/0.47    ~v4_relat_1(sK2,k2_struct_0(sK0)) | spl3_38),
% 0.21/0.47    inference(avatar_component_clause,[],[f220])).
% 0.21/0.47  fof(f220,plain,(
% 0.21/0.47    spl3_38 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.21/0.47  fof(f115,plain,(
% 0.21/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_15),
% 0.21/0.47    inference(avatar_component_clause,[],[f114])).
% 0.21/0.47  fof(f114,plain,(
% 0.21/0.47    spl3_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.47  fof(f225,plain,(
% 0.21/0.47    ~spl3_9 | ~spl3_13 | ~spl3_15 | spl3_37),
% 0.21/0.47    inference(avatar_contradiction_clause,[],[f223])).
% 0.21/0.47  fof(f223,plain,(
% 0.21/0.47    $false | (~spl3_9 | ~spl3_13 | ~spl3_15 | spl3_37)),
% 0.21/0.47    inference(unit_resulting_resolution,[],[f83,f115,f218,f99])).
% 0.21/0.47  fof(f99,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | ~spl3_13),
% 0.21/0.47    inference(avatar_component_clause,[],[f98])).
% 0.21/0.47  fof(f98,plain,(
% 0.21/0.47    spl3_13 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.47  fof(f218,plain,(
% 0.21/0.47    ~v1_relat_1(sK2) | spl3_37),
% 0.21/0.47    inference(avatar_component_clause,[],[f217])).
% 0.21/0.47  fof(f83,plain,(
% 0.21/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl3_9),
% 0.21/0.47    inference(avatar_component_clause,[],[f82])).
% 0.21/0.47  fof(f82,plain,(
% 0.21/0.47    spl3_9 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.47  fof(f222,plain,(
% 0.21/0.47    ~spl3_37 | ~spl3_38 | ~spl3_22 | spl3_31 | ~spl3_35),
% 0.21/0.47    inference(avatar_split_clause,[],[f215,f208,f190,f142,f220,f217])).
% 0.21/0.47  fof(f142,plain,(
% 0.21/0.47    spl3_22 <=> ! [X1,X0] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.47  fof(f190,plain,(
% 0.21/0.47    spl3_31 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.47  fof(f208,plain,(
% 0.21/0.47    spl3_35 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.21/0.47  fof(f215,plain,(
% 0.21/0.47    ~v4_relat_1(sK2,k2_struct_0(sK0)) | ~v1_relat_1(sK2) | (~spl3_22 | spl3_31 | ~spl3_35)),
% 0.21/0.47    inference(subsumption_resolution,[],[f214,f191])).
% 0.21/0.47  fof(f191,plain,(
% 0.21/0.47    k2_struct_0(sK0) != k1_relat_1(sK2) | spl3_31),
% 0.21/0.47    inference(avatar_component_clause,[],[f190])).
% 0.21/0.47  fof(f214,plain,(
% 0.21/0.47    ~v4_relat_1(sK2,k2_struct_0(sK0)) | k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl3_22 | ~spl3_35)),
% 0.21/0.47    inference(resolution,[],[f209,f143])).
% 0.21/0.47  fof(f143,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) ) | ~spl3_22),
% 0.21/0.47    inference(avatar_component_clause,[],[f142])).
% 0.21/0.47  fof(f209,plain,(
% 0.21/0.47    v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_35),
% 0.21/0.47    inference(avatar_component_clause,[],[f208])).
% 0.21/0.47  fof(f213,plain,(
% 0.21/0.47    spl3_35 | spl3_36 | ~spl3_14 | ~spl3_15 | ~spl3_33),
% 0.21/0.47    inference(avatar_split_clause,[],[f206,f198,f114,f110,f211,f208])).
% 0.21/0.47  fof(f110,plain,(
% 0.21/0.47    spl3_14 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.47  fof(f198,plain,(
% 0.21/0.47    spl3_33 <=> ! [X1,X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(sK2,X0,X1) | v1_partfun1(sK2,X0))),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.47  fof(f206,plain,(
% 0.21/0.47    v1_xboole_0(k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_14 | ~spl3_15 | ~spl3_33)),
% 0.21/0.47    inference(subsumption_resolution,[],[f205,f111])).
% 0.21/0.47  fof(f111,plain,(
% 0.21/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_14),
% 0.21/0.47    inference(avatar_component_clause,[],[f110])).
% 0.21/0.47  fof(f205,plain,(
% 0.21/0.47    v1_xboole_0(k2_struct_0(sK1)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_15 | ~spl3_33)),
% 0.21/0.47    inference(resolution,[],[f199,f115])).
% 0.21/0.47  fof(f199,plain,(
% 0.21/0.47    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(sK2,X0,X1) | v1_partfun1(sK2,X0)) ) | ~spl3_33),
% 0.21/0.47    inference(avatar_component_clause,[],[f198])).
% 0.21/0.47  fof(f200,plain,(
% 0.21/0.47    spl3_33 | ~spl3_1 | ~spl3_28),
% 0.21/0.47    inference(avatar_split_clause,[],[f179,f169,f51,f198])).
% 0.21/0.47  fof(f51,plain,(
% 0.21/0.47    spl3_1 <=> v1_funct_1(sK2)),
% 0.21/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    spl3_28 <=> ! [X1,X0,X2] : (v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.48  fof(f179,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(sK2,X0,X1) | v1_partfun1(sK2,X0)) ) | (~spl3_1 | ~spl3_28)),
% 0.21/0.48    inference(resolution,[],[f170,f52])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    v1_funct_1(sK2) | ~spl3_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f51])).
% 0.21/0.48  fof(f170,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) ) | ~spl3_28),
% 0.21/0.48    inference(avatar_component_clause,[],[f169])).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    ~spl3_31 | ~spl3_15 | ~spl3_23 | spl3_29 | ~spl3_30),
% 0.21/0.48    inference(avatar_split_clause,[],[f188,f181,f176,f146,f114,f190])).
% 0.21/0.48  fof(f146,plain,(
% 0.21/0.48    spl3_23 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.48  fof(f176,plain,(
% 0.21/0.48    spl3_29 <=> k2_struct_0(sK0) = k10_relat_1(sK2,k2_struct_0(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    spl3_30 <=> k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.48  fof(f188,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k1_relat_1(sK2) | (~spl3_15 | ~spl3_23 | spl3_29 | ~spl3_30)),
% 0.21/0.48    inference(backward_demodulation,[],[f177,f186])).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2) | (~spl3_15 | ~spl3_23 | ~spl3_30)),
% 0.21/0.48    inference(subsumption_resolution,[],[f184,f115])).
% 0.21/0.48  fof(f184,plain,(
% 0.21/0.48    k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_23 | ~spl3_30)),
% 0.21/0.48    inference(superposition,[],[f182,f147])).
% 0.21/0.48  fof(f147,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_23),
% 0.21/0.48    inference(avatar_component_clause,[],[f146])).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_30),
% 0.21/0.48    inference(avatar_component_clause,[],[f181])).
% 0.21/0.48  fof(f177,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1)) | spl3_29),
% 0.21/0.48    inference(avatar_component_clause,[],[f176])).
% 0.21/0.48  fof(f183,plain,(
% 0.21/0.48    spl3_30 | ~spl3_15 | ~spl3_26 | ~spl3_27),
% 0.21/0.48    inference(avatar_split_clause,[],[f174,f165,f160,f114,f181])).
% 0.21/0.48  fof(f160,plain,(
% 0.21/0.48    spl3_26 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.48  fof(f174,plain,(
% 0.21/0.48    k10_relat_1(sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_15 | ~spl3_26 | ~spl3_27)),
% 0.21/0.48    inference(forward_demodulation,[],[f173,f166])).
% 0.21/0.48  fof(f173,plain,(
% 0.21/0.48    k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_15 | ~spl3_26)),
% 0.21/0.48    inference(resolution,[],[f161,f115])).
% 0.21/0.48  fof(f161,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)) ) | ~spl3_26),
% 0.21/0.48    inference(avatar_component_clause,[],[f160])).
% 0.21/0.48  fof(f178,plain,(
% 0.21/0.48    ~spl3_29 | spl3_17 | ~spl3_27),
% 0.21/0.48    inference(avatar_split_clause,[],[f172,f165,f122,f176])).
% 0.21/0.48  fof(f172,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k10_relat_1(sK2,k2_struct_0(sK1)) | (spl3_17 | ~spl3_27)),
% 0.21/0.48    inference(superposition,[],[f123,f166])).
% 0.21/0.48  fof(f171,plain,(
% 0.21/0.48    spl3_28),
% 0.21/0.48    inference(avatar_split_clause,[],[f40,f169])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    spl3_27 | ~spl3_15 | ~spl3_24),
% 0.21/0.48    inference(avatar_split_clause,[],[f163,f152,f114,f165])).
% 0.21/0.48  fof(f152,plain,(
% 0.21/0.48    spl3_24 <=> ! [X1,X3,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.48  fof(f163,plain,(
% 0.21/0.48    ( ! [X0] : (k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,X0) = k10_relat_1(sK2,X0)) ) | (~spl3_15 | ~spl3_24)),
% 0.21/0.48    inference(resolution,[],[f153,f115])).
% 0.21/0.48  fof(f153,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) ) | ~spl3_24),
% 0.21/0.48    inference(avatar_component_clause,[],[f152])).
% 0.21/0.48  fof(f162,plain,(
% 0.21/0.48    spl3_26),
% 0.21/0.48    inference(avatar_split_clause,[],[f47,f160])).
% 0.21/0.48  fof(f47,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f8])).
% 0.21/0.48  fof(f8,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k8_relset_1(X0,X1,X2,X1) & k7_relset_1(X0,X1,X2,X0) = k2_relset_1(X0,X1,X2)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.21/0.48  fof(f154,plain,(
% 0.21/0.48    spl3_24),
% 0.21/0.48    inference(avatar_split_clause,[],[f48,f152])).
% 0.21/0.48  fof(f48,plain,(
% 0.21/0.48    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f7])).
% 0.21/0.48  fof(f7,axiom,(
% 0.21/0.48    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.48  fof(f148,plain,(
% 0.21/0.48    spl3_23),
% 0.21/0.48    inference(avatar_split_clause,[],[f43,f146])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f6])).
% 0.21/0.48  fof(f6,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f144,plain,(
% 0.21/0.48    spl3_22),
% 0.21/0.48    inference(avatar_split_clause,[],[f42,f142])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X1) | ~v4_relat_1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.48    inference(flattening,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.48    inference(ennf_transformation,[],[f10])).
% 0.21/0.48  fof(f10,axiom,(
% 0.21/0.48    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    spl3_19),
% 0.21/0.48    inference(avatar_split_clause,[],[f44,f130])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f5])).
% 0.21/0.48  fof(f5,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.48  fof(f124,plain,(
% 0.21/0.48    ~spl3_17 | ~spl3_2 | ~spl3_3 | spl3_8 | ~spl3_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f108,f90,f78,f59,f55,f122])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    spl3_2 <=> l1_struct_0(sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.48  fof(f59,plain,(
% 0.21/0.48    spl3_3 <=> l1_struct_0(sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    spl3_8 <=> k2_struct_0(sK0) = k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.48  fof(f90,plain,(
% 0.21/0.48    spl3_11 <=> ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.48  fof(f108,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k8_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (~spl3_2 | ~spl3_3 | spl3_8 | ~spl3_11)),
% 0.21/0.48    inference(backward_demodulation,[],[f103,f102])).
% 0.21/0.48  fof(f102,plain,(
% 0.21/0.48    k2_struct_0(sK0) = u1_struct_0(sK0) | (~spl3_3 | ~spl3_11)),
% 0.21/0.48    inference(resolution,[],[f91,f60])).
% 0.21/0.48  fof(f60,plain,(
% 0.21/0.48    l1_struct_0(sK0) | ~spl3_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f59])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl3_11),
% 0.21/0.48    inference(avatar_component_clause,[],[f90])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2,k2_struct_0(sK1)) | (~spl3_2 | spl3_8 | ~spl3_11)),
% 0.21/0.48    inference(backward_demodulation,[],[f79,f101])).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    k2_struct_0(sK1) = u1_struct_0(sK1) | (~spl3_2 | ~spl3_11)),
% 0.21/0.48    inference(resolution,[],[f91,f56])).
% 0.21/0.48  fof(f56,plain,(
% 0.21/0.48    l1_struct_0(sK1) | ~spl3_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f55])).
% 0.21/0.48  fof(f79,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1)) | spl3_8),
% 0.21/0.48    inference(avatar_component_clause,[],[f78])).
% 0.21/0.48  fof(f116,plain,(
% 0.21/0.48    spl3_15 | ~spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f107,f90,f74,f59,f55,f114])).
% 0.21/0.48  fof(f74,plain,(
% 0.21/0.48    spl3_7 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.48  fof(f107,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_2 | ~spl3_3 | ~spl3_7 | ~spl3_11)),
% 0.21/0.48    inference(backward_demodulation,[],[f104,f102])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_2 | ~spl3_7 | ~spl3_11)),
% 0.21/0.48    inference(backward_demodulation,[],[f75,f101])).
% 0.21/0.48  fof(f75,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_7),
% 0.21/0.48    inference(avatar_component_clause,[],[f74])).
% 0.21/0.48  fof(f112,plain,(
% 0.21/0.48    spl3_14 | ~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f106,f90,f63,f59,f55,f110])).
% 0.21/0.48  fof(f63,plain,(
% 0.21/0.48    spl3_4 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.48  fof(f106,plain,(
% 0.21/0.48    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_2 | ~spl3_3 | ~spl3_4 | ~spl3_11)),
% 0.21/0.48    inference(backward_demodulation,[],[f105,f102])).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_2 | ~spl3_4 | ~spl3_11)),
% 0.21/0.48    inference(backward_demodulation,[],[f64,f101])).
% 0.21/0.48  fof(f64,plain,(
% 0.21/0.48    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f63])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    spl3_13),
% 0.21/0.48    inference(avatar_split_clause,[],[f38,f98])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,plain,(
% 0.21/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    spl3_12),
% 0.21/0.48    inference(avatar_split_clause,[],[f37,f94])).
% 0.21/0.48  fof(f37,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | k1_xboole_0 = k10_relat_1(X0,k1_xboole_0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f18])).
% 0.21/0.48  fof(f18,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = k10_relat_1(X0,k1_xboole_0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0] : (v1_relat_1(X0) => k1_xboole_0 = k10_relat_1(X0,k1_xboole_0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t171_relat_1)).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    spl3_11),
% 0.21/0.48    inference(avatar_split_clause,[],[f36,f90])).
% 0.21/0.48  fof(f36,plain,(
% 0.21/0.48    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,plain,(
% 0.21/0.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    spl3_10),
% 0.21/0.48    inference(avatar_split_clause,[],[f35,f86])).
% 0.21/0.48  fof(f35,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f16])).
% 0.21/0.48  fof(f16,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f1])).
% 0.21/0.48  fof(f1,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    spl3_9),
% 0.21/0.48    inference(avatar_split_clause,[],[f39,f82])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f3])).
% 0.21/0.48  % (14240)Refutation not found, incomplete strategy% (14240)------------------------------
% 0.21/0.48  % (14240)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (14240)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (14240)Memory used [KB]: 10746
% 0.21/0.48  % (14240)Time elapsed: 0.068 s
% 0.21/0.48  % (14240)------------------------------
% 0.21/0.48  % (14240)------------------------------
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.48  fof(f80,plain,(
% 0.21/0.48    ~spl3_8),
% 0.21/0.48    inference(avatar_split_clause,[],[f32,f78])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    k2_struct_0(sK0) != k8_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_struct_0(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : (k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1)) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.48    inference(flattening,[],[f14])).
% 0.21/0.48  fof(f14,plain,(
% 0.21/0.48    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1)) & (k1_xboole_0 = k2_struct_0(X0) | k1_xboole_0 != k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,negated_conjecture,(
% 0.21/0.48    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.21/0.48    inference(negated_conjecture,[],[f12])).
% 0.21/0.48  fof(f12,conjecture,(
% 0.21/0.48    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((k1_xboole_0 = k2_struct_0(X1) => k1_xboole_0 = k2_struct_0(X0)) => k2_struct_0(X0) = k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_struct_0(X1))))))),
% 0.21/0.48    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_tops_2)).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    spl3_7),
% 0.21/0.48    inference(avatar_split_clause,[],[f31,f74])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    spl3_5 | ~spl3_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f28,f70,f67])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    k1_xboole_0 != k2_struct_0(sK1) | k1_xboole_0 = k2_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    spl3_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f30,f63])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f61,plain,(
% 0.21/0.48    spl3_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f34,f59])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    l1_struct_0(sK0)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f57,plain,(
% 0.21/0.48    spl3_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f33,f55])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    l1_struct_0(sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    spl3_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f29,f51])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    v1_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f15])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (14247)------------------------------
% 0.21/0.48  % (14247)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (14247)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (14247)Memory used [KB]: 10746
% 0.21/0.48  % (14247)Time elapsed: 0.062 s
% 0.21/0.48  % (14247)------------------------------
% 0.21/0.48  % (14247)------------------------------
% 0.21/0.48  % (14237)Success in time 0.117 s
%------------------------------------------------------------------------------
