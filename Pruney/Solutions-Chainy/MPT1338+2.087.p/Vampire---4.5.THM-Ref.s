%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:13 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  279 ( 626 expanded)
%              Number of leaves         :   67 ( 296 expanded)
%              Depth                    :   10
%              Number of atoms          :  922 (2051 expanded)
%              Number of equality atoms :  174 ( 456 expanded)
%              Maximal formula depth    :   11 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f613,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f70,f74,f78,f82,f86,f90,f94,f98,f102,f106,f110,f114,f118,f134,f142,f146,f157,f161,f165,f169,f173,f177,f181,f190,f203,f210,f214,f218,f224,f232,f236,f240,f252,f261,f274,f278,f296,f316,f337,f342,f351,f359,f370,f374,f386,f394,f459,f462,f479,f498,f518,f527,f594,f612])).

fof(f612,plain,
    ( ~ spl3_68
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_22
    | spl3_88 ),
    inference(avatar_split_clause,[],[f602,f592,f163,f72,f68,f454])).

fof(f454,plain,
    ( spl3_68
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).

fof(f68,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f72,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f163,plain,
    ( spl3_22
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f592,plain,
    ( spl3_88
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_88])])).

fof(f602,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_22
    | spl3_88 ),
    inference(subsumption_resolution,[],[f601,f73])).

fof(f73,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f72])).

fof(f601,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_22
    | spl3_88 ),
    inference(subsumption_resolution,[],[f600,f69])).

fof(f69,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f68])).

fof(f600,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_22
    | spl3_88 ),
    inference(trivial_inequality_removal,[],[f599])).

fof(f599,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_22
    | spl3_88 ),
    inference(superposition,[],[f593,f164])).

fof(f164,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f163])).

fof(f593,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | spl3_88 ),
    inference(avatar_component_clause,[],[f592])).

fof(f594,plain,
    ( ~ spl3_88
    | spl3_57
    | ~ spl3_77 ),
    inference(avatar_split_clause,[],[f590,f525,f384,f592])).

fof(f384,plain,
    ( spl3_57
  <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f525,plain,
    ( spl3_77
  <=> k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).

fof(f590,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | spl3_57
    | ~ spl3_77 ),
    inference(superposition,[],[f385,f526])).

fof(f526,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_77 ),
    inference(avatar_component_clause,[],[f525])).

fof(f385,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | spl3_57 ),
    inference(avatar_component_clause,[],[f384])).

fof(f527,plain,
    ( spl3_77
    | ~ spl3_25
    | ~ spl3_69 ),
    inference(avatar_split_clause,[],[f465,f457,f175,f525])).

fof(f175,plain,
    ( spl3_25
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f457,plain,
    ( spl3_69
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f465,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_25
    | ~ spl3_69 ),
    inference(resolution,[],[f458,f176])).

fof(f176,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) )
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f175])).

fof(f458,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_69 ),
    inference(avatar_component_clause,[],[f457])).

fof(f518,plain,
    ( ~ spl3_68
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_23
    | spl3_74 ),
    inference(avatar_split_clause,[],[f509,f496,f167,f72,f68,f454])).

fof(f167,plain,
    ( spl3_23
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f496,plain,
    ( spl3_74
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).

fof(f509,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_23
    | spl3_74 ),
    inference(subsumption_resolution,[],[f508,f73])).

fof(f508,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_23
    | spl3_74 ),
    inference(subsumption_resolution,[],[f507,f69])).

fof(f507,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_23
    | spl3_74 ),
    inference(trivial_inequality_removal,[],[f506])).

fof(f506,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_23
    | spl3_74 ),
    inference(superposition,[],[f497,f168])).

fof(f168,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f167])).

fof(f497,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | spl3_74 ),
    inference(avatar_component_clause,[],[f496])).

fof(f498,plain,
    ( ~ spl3_74
    | spl3_59
    | ~ spl3_71 ),
    inference(avatar_split_clause,[],[f484,f477,f392,f496])).

fof(f392,plain,
    ( spl3_59
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f477,plain,
    ( spl3_71
  <=> k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).

fof(f484,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | spl3_59
    | ~ spl3_71 ),
    inference(superposition,[],[f393,f478])).

fof(f478,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_71 ),
    inference(avatar_component_clause,[],[f477])).

fof(f393,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | spl3_59 ),
    inference(avatar_component_clause,[],[f392])).

fof(f479,plain,
    ( spl3_71
    | ~ spl3_26
    | ~ spl3_69 ),
    inference(avatar_split_clause,[],[f464,f457,f179,f477])).

fof(f179,plain,
    ( spl3_26
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f464,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_26
    | ~ spl3_69 ),
    inference(resolution,[],[f458,f180])).

fof(f180,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) )
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f179])).

fof(f462,plain,
    ( ~ spl3_10
    | ~ spl3_13
    | ~ spl3_49
    | spl3_68 ),
    inference(avatar_contradiction_clause,[],[f460])).

fof(f460,plain,
    ( $false
    | ~ spl3_10
    | ~ spl3_13
    | ~ spl3_49
    | spl3_68 ),
    inference(unit_resulting_resolution,[],[f105,f341,f455,f117])).

fof(f117,plain,
    ( ! [X0,X1] :
        ( v1_relat_1(X1)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f116])).

fof(f116,plain,
    ( spl3_13
  <=> ! [X1,X0] :
        ( ~ v1_relat_1(X0)
        | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
        | v1_relat_1(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f455,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_68 ),
    inference(avatar_component_clause,[],[f454])).

fof(f341,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f340])).

fof(f340,plain,
    ( spl3_49
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f105,plain,
    ( ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f104])).

fof(f104,plain,
    ( spl3_10
  <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f459,plain,
    ( ~ spl3_68
    | spl3_69
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_21
    | ~ spl3_44
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f332,f294,f272,f159,f72,f68,f457,f454])).

fof(f159,plain,
    ( spl3_21
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k2_funct_1(X0) = k4_relat_1(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f272,plain,
    ( spl3_44
  <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f294,plain,
    ( spl3_47
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f332,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_21
    | ~ spl3_44
    | ~ spl3_47 ),
    inference(backward_demodulation,[],[f284,f295])).

fof(f295,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f294])).

% (21147)Refutation not found, incomplete strategy% (21147)------------------------------
% (21147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% (21147)Termination reason: Refutation not found, incomplete strategy

% (21147)Memory used [KB]: 10618
% (21147)Time elapsed: 0.065 s
% (21147)------------------------------
% (21147)------------------------------
fof(f284,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_21
    | ~ spl3_44 ),
    inference(subsumption_resolution,[],[f283,f73])).

fof(f283,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_21
    | ~ spl3_44 ),
    inference(subsumption_resolution,[],[f282,f69])).

fof(f282,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_21
    | ~ spl3_44 ),
    inference(superposition,[],[f273,f160])).

fof(f160,plain,
    ( ! [X0] :
        ( k2_funct_1(X0) = k4_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f159])).

fof(f273,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f272])).

fof(f394,plain,
    ( ~ spl3_59
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_48
    | ~ spl3_49
    | spl3_50
    | ~ spl3_55
    | ~ spl3_56 ),
    inference(avatar_split_clause,[],[f382,f372,f368,f349,f340,f335,f72,f68,f392])).

fof(f335,plain,
    ( spl3_48
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f349,plain,
    ( spl3_50
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f368,plain,
    ( spl3_55
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) != X1
        | ~ v2_funct_1(X2)
        | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).

fof(f372,plain,
    ( spl3_56
  <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f382,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_48
    | ~ spl3_49
    | spl3_50
    | ~ spl3_55
    | ~ spl3_56 ),
    inference(backward_demodulation,[],[f350,f380])).

fof(f380,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_48
    | ~ spl3_49
    | ~ spl3_55
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f379,f73])).

fof(f379,plain,
    ( ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_1
    | ~ spl3_48
    | ~ spl3_49
    | ~ spl3_55
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f378,f69])).

fof(f378,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_48
    | ~ spl3_49
    | ~ spl3_55
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f377,f341])).

fof(f377,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_48
    | ~ spl3_55
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f376,f336])).

fof(f336,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_48 ),
    inference(avatar_component_clause,[],[f335])).

fof(f376,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_55
    | ~ spl3_56 ),
    inference(trivial_inequality_removal,[],[f375])).

fof(f375,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_55
    | ~ spl3_56 ),
    inference(superposition,[],[f369,f373])).

fof(f373,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f372])).

fof(f369,plain,
    ( ! [X2,X0,X1] :
        ( k2_relset_1(X0,X1,X2) != X1
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ v2_funct_1(X2)
        | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) )
    | ~ spl3_55 ),
    inference(avatar_component_clause,[],[f368])).

fof(f350,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | spl3_50 ),
    inference(avatar_component_clause,[],[f349])).

fof(f386,plain,
    ( ~ spl3_57
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_48
    | ~ spl3_49
    | spl3_52
    | ~ spl3_55
    | ~ spl3_56 ),
    inference(avatar_split_clause,[],[f381,f372,f368,f357,f340,f335,f72,f68,f384])).

fof(f357,plain,
    ( spl3_52
  <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f381,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_48
    | ~ spl3_49
    | spl3_52
    | ~ spl3_55
    | ~ spl3_56 ),
    inference(backward_demodulation,[],[f358,f380])).

fof(f358,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | spl3_52 ),
    inference(avatar_component_clause,[],[f357])).

fof(f374,plain,
    ( spl3_56
    | ~ spl3_36
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f322,f294,f234,f372])).

fof(f234,plain,
    ( spl3_36
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f322,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_36
    | ~ spl3_47 ),
    inference(backward_demodulation,[],[f235,f295])).

fof(f235,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f234])).

fof(f370,plain,(
    spl3_55 ),
    inference(avatar_split_clause,[],[f61,f368])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f359,plain,
    ( ~ spl3_52
    | spl3_35
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f321,f294,f230,f357])).

fof(f230,plain,
    ( spl3_35
  <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f321,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | spl3_35
    | ~ spl3_47 ),
    inference(backward_demodulation,[],[f231,f295])).

fof(f231,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl3_35 ),
    inference(avatar_component_clause,[],[f230])).

fof(f351,plain,
    ( ~ spl3_50
    | spl3_33
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f320,f294,f222,f349])).

fof(f222,plain,
    ( spl3_33
  <=> k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

% (21132)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f320,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | spl3_33
    | ~ spl3_47 ),
    inference(backward_demodulation,[],[f223,f295])).

fof(f223,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl3_33 ),
    inference(avatar_component_clause,[],[f222])).

fof(f342,plain,
    ( spl3_49
    | ~ spl3_31
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f319,f294,f212,f340])).

fof(f212,plain,
    ( spl3_31
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f319,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_31
    | ~ spl3_47 ),
    inference(backward_demodulation,[],[f213,f295])).

fof(f213,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f212])).

fof(f337,plain,
    ( spl3_48
    | ~ spl3_30
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f318,f294,f208,f335])).

fof(f208,plain,
    ( spl3_30
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f318,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_30
    | ~ spl3_47 ),
    inference(backward_demodulation,[],[f209,f295])).

fof(f209,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f208])).

fof(f316,plain,
    ( ~ spl3_7
    | spl3_32
    | ~ spl3_46 ),
    inference(avatar_contradiction_clause,[],[f315])).

fof(f315,plain,
    ( $false
    | ~ spl3_7
    | spl3_32
    | ~ spl3_46 ),
    inference(subsumption_resolution,[],[f300,f93])).

fof(f93,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f92])).

fof(f92,plain,
    ( spl3_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f300,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_32
    | ~ spl3_46 ),
    inference(backward_demodulation,[],[f217,f292])).

fof(f292,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f291])).

fof(f291,plain,
    ( spl3_46
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f217,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_32 ),
    inference(avatar_component_clause,[],[f216])).

fof(f216,plain,
    ( spl3_32
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f296,plain,
    ( spl3_46
    | spl3_47
    | ~ spl3_30
    | ~ spl3_31
    | ~ spl3_40
    | ~ spl3_45 ),
    inference(avatar_split_clause,[],[f289,f276,f250,f212,f208,f294,f291])).

fof(f250,plain,
    ( spl3_40
  <=> k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f276,plain,
    ( spl3_45
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f289,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl3_30
    | ~ spl3_31
    | ~ spl3_40
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f288,f251])).

fof(f251,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f250])).

fof(f288,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_30
    | ~ spl3_31
    | ~ spl3_45 ),
    inference(subsumption_resolution,[],[f285,f213])).

fof(f285,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_30
    | ~ spl3_45 ),
    inference(resolution,[],[f277,f209])).

fof(f277,plain,
    ( ! [X2,X0,X1] :
        ( ~ v1_funct_2(X2,X0,X1)
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f276])).

fof(f278,plain,(
    spl3_45 ),
    inference(avatar_split_clause,[],[f60,f276])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
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
    inference(flattening,[],[f30])).

fof(f30,plain,(
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
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).

fof(f274,plain,
    ( spl3_44
    | ~ spl3_24
    | ~ spl3_31
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f266,f259,f212,f171,f272])).

fof(f171,plain,
    ( spl3_24
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f259,plain,
    ( spl3_42
  <=> m1_subset_1(k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f266,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_24
    | ~ spl3_31
    | ~ spl3_42 ),
    inference(subsumption_resolution,[],[f265,f213])).

fof(f265,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_24
    | ~ spl3_42 ),
    inference(superposition,[],[f260,f172])).

fof(f172,plain,
    ( ! [X2,X0,X1] :
        ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f171])).

fof(f260,plain,
    ( m1_subset_1(k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f259])).

fof(f261,plain,
    ( spl3_42
    | ~ spl3_31
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f257,f238,f212,f259])).

fof(f238,plain,
    ( spl3_37
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f257,plain,
    ( m1_subset_1(k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_31
    | ~ spl3_37 ),
    inference(resolution,[],[f239,f213])).

fof(f239,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f238])).

fof(f252,plain,
    ( spl3_40
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_26
    | ~ spl3_28 ),
    inference(avatar_split_clause,[],[f198,f188,f179,f144,f140,f250])).

fof(f140,plain,
    ( spl3_16
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f144,plain,
    ( spl3_17
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f188,plain,
    ( spl3_28
  <=> k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f198,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_26
    | ~ spl3_28 ),
    inference(backward_demodulation,[],[f189,f192])).

fof(f192,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_26 ),
    inference(backward_demodulation,[],[f145,f191])).

fof(f191,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_16
    | ~ spl3_26 ),
    inference(resolution,[],[f180,f141])).

fof(f141,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f140])).

fof(f145,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f144])).

fof(f189,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f188])).

fof(f240,plain,(
    spl3_37 ),
    inference(avatar_split_clause,[],[f54,f238])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).

fof(f236,plain,
    ( spl3_36
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f199,f179,f144,f140,f234])).

fof(f199,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_26 ),
    inference(backward_demodulation,[],[f191,f192])).

fof(f232,plain,
    ( ~ spl3_35
    | ~ spl3_16
    | ~ spl3_17
    | spl3_20
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f197,f179,f155,f144,f140,f230])).

fof(f155,plain,
    ( spl3_20
  <=> k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f197,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | ~ spl3_16
    | ~ spl3_17
    | spl3_20
    | ~ spl3_26 ),
    inference(backward_demodulation,[],[f156,f192])).

fof(f156,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_20 ),
    inference(avatar_component_clause,[],[f155])).

fof(f224,plain,
    ( ~ spl3_33
    | ~ spl3_16
    | ~ spl3_17
    | spl3_19
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f196,f179,f152,f144,f140,f222])).

fof(f152,plain,
    ( spl3_19
  <=> k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f196,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | ~ spl3_16
    | ~ spl3_17
    | spl3_19
    | ~ spl3_26 ),
    inference(backward_demodulation,[],[f153,f192])).

fof(f153,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f152])).

fof(f218,plain,
    ( ~ spl3_32
    | spl3_3
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f206,f201,f112,f80,f76,f216])).

fof(f76,plain,
    ( spl3_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f80,plain,
    ( spl3_4
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f112,plain,
    ( spl3_12
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f201,plain,
    ( spl3_29
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f206,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_3
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f205,f77])).

fof(f77,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f76])).

fof(f205,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | v2_struct_0(sK1)
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_29 ),
    inference(subsumption_resolution,[],[f204,f81])).

fof(f81,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f80])).

fof(f204,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_12
    | ~ spl3_29 ),
    inference(superposition,[],[f113,f202])).

fof(f202,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f201])).

fof(f113,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k2_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f112])).

fof(f214,plain,
    ( spl3_31
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f195,f179,f144,f140,f212])).

fof(f195,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_26 ),
    inference(backward_demodulation,[],[f141,f192])).

fof(f210,plain,
    ( spl3_30
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f193,f179,f144,f140,f132,f208])).

fof(f132,plain,
    ( spl3_14
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f193,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_26 ),
    inference(backward_demodulation,[],[f133,f192])).

fof(f133,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f132])).

fof(f203,plain,
    ( spl3_29
    | ~ spl3_16
    | ~ spl3_17
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f192,f179,f144,f140,f201])).

fof(f190,plain,
    ( spl3_28
    | ~ spl3_16
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f186,f175,f140,f188])).

fof(f186,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2)
    | ~ spl3_16
    | ~ spl3_25 ),
    inference(resolution,[],[f176,f141])).

fof(f181,plain,(
    spl3_26 ),
    inference(avatar_split_clause,[],[f53,f179])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f177,plain,(
    spl3_25 ),
    inference(avatar_split_clause,[],[f52,f175])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f173,plain,(
    spl3_24 ),
    inference(avatar_split_clause,[],[f51,f171])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(f169,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f49,f167])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f165,plain,(
    spl3_22 ),
    inference(avatar_split_clause,[],[f48,f163])).

fof(f48,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f161,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f47,f159])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_funct_1(X0) = k4_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(X0) = k4_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f157,plain,
    ( ~ spl3_19
    | ~ spl3_20
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f130,f108,f84,f80,f155,f152])).

fof(f84,plain,
    ( spl3_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f108,plain,
    ( spl3_11
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f130,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f126,f120])).

fof(f120,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(resolution,[],[f109,f85])).

fof(f85,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f84])).

fof(f109,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f108])).

fof(f126,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f125,f120])).

fof(f125,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f124,f119])).

fof(f119,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(resolution,[],[f109,f81])).

fof(f124,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f34,f119])).

fof(f34,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( ( l1_struct_0(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                    & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f14])).

fof(f14,conjecture,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( ( l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).

fof(f146,plain,
    ( spl3_17
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f129,f108,f100,f84,f80,f144])).

fof(f100,plain,
    ( spl3_9
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f129,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f121,f120])).

fof(f121,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f101,f119])).

fof(f101,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f100])).

fof(f142,plain,
    ( spl3_16
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f128,f108,f96,f84,f80,f140])).

fof(f96,plain,
    ( spl3_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f128,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f122,f120])).

fof(f122,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f97,f119])).

fof(f97,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f96])).

fof(f134,plain,
    ( spl3_14
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f127,f108,f88,f84,f80,f132])).

fof(f88,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f127,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f123,f120])).

fof(f123,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(backward_demodulation,[],[f89,f119])).

fof(f89,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f88])).

fof(f118,plain,(
    spl3_13 ),
    inference(avatar_split_clause,[],[f45,f116])).

fof(f45,plain,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f114,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f46,f112])).

fof(f46,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f110,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f44,f108])).

fof(f44,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f106,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f50,f104])).

fof(f50,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f102,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f38,f100])).

fof(f38,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f98,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f37,f96])).

fof(f37,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f17])).

fof(f94,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f43,f92])).

fof(f43,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f90,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f36,f88])).

fof(f36,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f17])).

fof(f86,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f42,f84])).

fof(f42,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f17])).

fof(f82,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f41,f80])).

fof(f41,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f78,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f40,f76])).

fof(f40,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f17])).

fof(f74,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f39,f72])).

fof(f39,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).

fof(f70,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f35,f68])).

fof(f35,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f17])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 17:25:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.46  % (21147)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.46  % (21136)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.46  % (21131)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.46  % (21141)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.46  % (21133)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.47  % (21140)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.47  % (21136)Refutation found. Thanks to Tanya!
% 0.20/0.47  % SZS status Theorem for theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f613,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f70,f74,f78,f82,f86,f90,f94,f98,f102,f106,f110,f114,f118,f134,f142,f146,f157,f161,f165,f169,f173,f177,f181,f190,f203,f210,f214,f218,f224,f232,f236,f240,f252,f261,f274,f278,f296,f316,f337,f342,f351,f359,f370,f374,f386,f394,f459,f462,f479,f498,f518,f527,f594,f612])).
% 0.20/0.47  fof(f612,plain,(
% 0.20/0.47    ~spl3_68 | ~spl3_1 | ~spl3_2 | ~spl3_22 | spl3_88),
% 0.20/0.47    inference(avatar_split_clause,[],[f602,f592,f163,f72,f68,f454])).
% 0.20/0.47  fof(f454,plain,(
% 0.20/0.47    spl3_68 <=> v1_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_68])])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    spl3_1 <=> v1_funct_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    spl3_2 <=> v2_funct_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    spl3_22 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.47  fof(f592,plain,(
% 0.20/0.47    spl3_88 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_88])])).
% 0.20/0.47  fof(f602,plain,(
% 0.20/0.47    ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_2 | ~spl3_22 | spl3_88)),
% 0.20/0.47    inference(subsumption_resolution,[],[f601,f73])).
% 0.20/0.47  fof(f73,plain,(
% 0.20/0.47    v2_funct_1(sK2) | ~spl3_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f72])).
% 0.20/0.47  fof(f601,plain,(
% 0.20/0.47    ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_22 | spl3_88)),
% 0.20/0.47    inference(subsumption_resolution,[],[f600,f69])).
% 0.20/0.47  fof(f69,plain,(
% 0.20/0.47    v1_funct_1(sK2) | ~spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f68])).
% 0.20/0.47  fof(f600,plain,(
% 0.20/0.47    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_22 | spl3_88)),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f599])).
% 0.20/0.47  fof(f599,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_22 | spl3_88)),
% 0.20/0.47    inference(superposition,[],[f593,f164])).
% 0.20/0.47  fof(f164,plain,(
% 0.20/0.47    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_22),
% 0.20/0.47    inference(avatar_component_clause,[],[f163])).
% 0.20/0.47  fof(f593,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | spl3_88),
% 0.20/0.47    inference(avatar_component_clause,[],[f592])).
% 0.20/0.47  fof(f594,plain,(
% 0.20/0.47    ~spl3_88 | spl3_57 | ~spl3_77),
% 0.20/0.47    inference(avatar_split_clause,[],[f590,f525,f384,f592])).
% 0.20/0.47  fof(f384,plain,(
% 0.20/0.47    spl3_57 <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.20/0.47  fof(f525,plain,(
% 0.20/0.47    spl3_77 <=> k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).
% 0.20/0.47  fof(f590,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | (spl3_57 | ~spl3_77)),
% 0.20/0.47    inference(superposition,[],[f385,f526])).
% 0.20/0.47  fof(f526,plain,(
% 0.20/0.47    k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_77),
% 0.20/0.47    inference(avatar_component_clause,[],[f525])).
% 0.20/0.47  fof(f385,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | spl3_57),
% 0.20/0.47    inference(avatar_component_clause,[],[f384])).
% 0.20/0.47  fof(f527,plain,(
% 0.20/0.47    spl3_77 | ~spl3_25 | ~spl3_69),
% 0.20/0.47    inference(avatar_split_clause,[],[f465,f457,f175,f525])).
% 0.20/0.47  fof(f175,plain,(
% 0.20/0.47    spl3_25 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.47  fof(f457,plain,(
% 0.20/0.47    spl3_69 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 0.20/0.47  fof(f465,plain,(
% 0.20/0.47    k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_25 | ~spl3_69)),
% 0.20/0.47    inference(resolution,[],[f458,f176])).
% 0.20/0.47  fof(f176,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) ) | ~spl3_25),
% 0.20/0.47    inference(avatar_component_clause,[],[f175])).
% 0.20/0.47  fof(f458,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_69),
% 0.20/0.47    inference(avatar_component_clause,[],[f457])).
% 0.20/0.47  fof(f518,plain,(
% 0.20/0.47    ~spl3_68 | ~spl3_1 | ~spl3_2 | ~spl3_23 | spl3_74),
% 0.20/0.47    inference(avatar_split_clause,[],[f509,f496,f167,f72,f68,f454])).
% 0.20/0.47  fof(f167,plain,(
% 0.20/0.47    spl3_23 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.47  fof(f496,plain,(
% 0.20/0.47    spl3_74 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).
% 0.20/0.47  fof(f509,plain,(
% 0.20/0.47    ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_2 | ~spl3_23 | spl3_74)),
% 0.20/0.47    inference(subsumption_resolution,[],[f508,f73])).
% 0.20/0.47  fof(f508,plain,(
% 0.20/0.47    ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_23 | spl3_74)),
% 0.20/0.47    inference(subsumption_resolution,[],[f507,f69])).
% 0.20/0.47  fof(f507,plain,(
% 0.20/0.47    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_23 | spl3_74)),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f506])).
% 0.20/0.47  fof(f506,plain,(
% 0.20/0.47    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_23 | spl3_74)),
% 0.20/0.47    inference(superposition,[],[f497,f168])).
% 0.20/0.47  fof(f168,plain,(
% 0.20/0.47    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_23),
% 0.20/0.47    inference(avatar_component_clause,[],[f167])).
% 0.20/0.47  fof(f497,plain,(
% 0.20/0.47    k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | spl3_74),
% 0.20/0.47    inference(avatar_component_clause,[],[f496])).
% 0.20/0.47  fof(f498,plain,(
% 0.20/0.47    ~spl3_74 | spl3_59 | ~spl3_71),
% 0.20/0.47    inference(avatar_split_clause,[],[f484,f477,f392,f496])).
% 0.20/0.47  fof(f392,plain,(
% 0.20/0.47    spl3_59 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 0.20/0.47  fof(f477,plain,(
% 0.20/0.47    spl3_71 <=> k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).
% 0.20/0.47  fof(f484,plain,(
% 0.20/0.47    k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | (spl3_59 | ~spl3_71)),
% 0.20/0.47    inference(superposition,[],[f393,f478])).
% 0.20/0.47  fof(f478,plain,(
% 0.20/0.47    k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_71),
% 0.20/0.47    inference(avatar_component_clause,[],[f477])).
% 0.20/0.47  fof(f393,plain,(
% 0.20/0.47    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | spl3_59),
% 0.20/0.47    inference(avatar_component_clause,[],[f392])).
% 0.20/0.47  fof(f479,plain,(
% 0.20/0.47    spl3_71 | ~spl3_26 | ~spl3_69),
% 0.20/0.47    inference(avatar_split_clause,[],[f464,f457,f179,f477])).
% 0.20/0.47  fof(f179,plain,(
% 0.20/0.47    spl3_26 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.20/0.47  fof(f464,plain,(
% 0.20/0.47    k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_26 | ~spl3_69)),
% 0.20/0.47    inference(resolution,[],[f458,f180])).
% 0.20/0.47  fof(f180,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) ) | ~spl3_26),
% 0.20/0.47    inference(avatar_component_clause,[],[f179])).
% 0.20/0.47  fof(f462,plain,(
% 0.20/0.47    ~spl3_10 | ~spl3_13 | ~spl3_49 | spl3_68),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f460])).
% 0.20/0.47  fof(f460,plain,(
% 0.20/0.47    $false | (~spl3_10 | ~spl3_13 | ~spl3_49 | spl3_68)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f105,f341,f455,f117])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | ~spl3_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f116])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    spl3_13 <=> ! [X1,X0] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.47  fof(f455,plain,(
% 0.20/0.47    ~v1_relat_1(sK2) | spl3_68),
% 0.20/0.47    inference(avatar_component_clause,[],[f454])).
% 0.20/0.47  fof(f341,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_49),
% 0.20/0.47    inference(avatar_component_clause,[],[f340])).
% 0.20/0.47  fof(f340,plain,(
% 0.20/0.47    spl3_49 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.20/0.47  fof(f105,plain,(
% 0.20/0.47    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) ) | ~spl3_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f104])).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    spl3_10 <=> ! [X1,X0] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.47  fof(f459,plain,(
% 0.20/0.47    ~spl3_68 | spl3_69 | ~spl3_1 | ~spl3_2 | ~spl3_21 | ~spl3_44 | ~spl3_47),
% 0.20/0.47    inference(avatar_split_clause,[],[f332,f294,f272,f159,f72,f68,f457,f454])).
% 0.20/0.47  fof(f159,plain,(
% 0.20/0.47    spl3_21 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_funct_1(X0) = k4_relat_1(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.47  fof(f272,plain,(
% 0.20/0.47    spl3_44 <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.20/0.47  fof(f294,plain,(
% 0.20/0.47    spl3_47 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.20/0.47  fof(f332,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_2 | ~spl3_21 | ~spl3_44 | ~spl3_47)),
% 0.20/0.47    inference(backward_demodulation,[],[f284,f295])).
% 0.20/0.47  fof(f295,plain,(
% 0.20/0.47    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_47),
% 0.20/0.47    inference(avatar_component_clause,[],[f294])).
% 0.20/0.47  % (21147)Refutation not found, incomplete strategy% (21147)------------------------------
% 0.20/0.47  % (21147)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.47  % (21147)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.47  
% 0.20/0.47  % (21147)Memory used [KB]: 10618
% 0.20/0.47  % (21147)Time elapsed: 0.065 s
% 0.20/0.47  % (21147)------------------------------
% 0.20/0.47  % (21147)------------------------------
% 0.20/0.47  fof(f284,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_2 | ~spl3_21 | ~spl3_44)),
% 0.20/0.47    inference(subsumption_resolution,[],[f283,f73])).
% 0.20/0.47  fof(f283,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_21 | ~spl3_44)),
% 0.20/0.47    inference(subsumption_resolution,[],[f282,f69])).
% 0.20/0.47  fof(f282,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_21 | ~spl3_44)),
% 0.20/0.47    inference(superposition,[],[f273,f160])).
% 0.20/0.47  fof(f160,plain,(
% 0.20/0.47    ( ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_21),
% 0.20/0.47    inference(avatar_component_clause,[],[f159])).
% 0.20/0.47  fof(f273,plain,(
% 0.20/0.47    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~spl3_44),
% 0.20/0.47    inference(avatar_component_clause,[],[f272])).
% 0.20/0.47  fof(f394,plain,(
% 0.20/0.47    ~spl3_59 | ~spl3_1 | ~spl3_2 | ~spl3_48 | ~spl3_49 | spl3_50 | ~spl3_55 | ~spl3_56),
% 0.20/0.47    inference(avatar_split_clause,[],[f382,f372,f368,f349,f340,f335,f72,f68,f392])).
% 0.20/0.47  fof(f335,plain,(
% 0.20/0.47    spl3_48 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.20/0.47  fof(f349,plain,(
% 0.20/0.47    spl3_50 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.20/0.47  fof(f368,plain,(
% 0.20/0.47    spl3_55 <=> ! [X1,X0,X2] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_tops_2(X0,X1,X2) = k2_funct_1(X2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_55])])).
% 0.20/0.47  fof(f372,plain,(
% 0.20/0.47    spl3_56 <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.20/0.47  fof(f382,plain,(
% 0.20/0.47    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_48 | ~spl3_49 | spl3_50 | ~spl3_55 | ~spl3_56)),
% 0.20/0.47    inference(backward_demodulation,[],[f350,f380])).
% 0.20/0.47  fof(f380,plain,(
% 0.20/0.47    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_2 | ~spl3_48 | ~spl3_49 | ~spl3_55 | ~spl3_56)),
% 0.20/0.47    inference(subsumption_resolution,[],[f379,f73])).
% 0.20/0.47  fof(f379,plain,(
% 0.20/0.47    ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_1 | ~spl3_48 | ~spl3_49 | ~spl3_55 | ~spl3_56)),
% 0.20/0.47    inference(subsumption_resolution,[],[f378,f69])).
% 0.20/0.47  fof(f378,plain,(
% 0.20/0.47    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_48 | ~spl3_49 | ~spl3_55 | ~spl3_56)),
% 0.20/0.47    inference(subsumption_resolution,[],[f377,f341])).
% 0.20/0.47  fof(f377,plain,(
% 0.20/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_48 | ~spl3_55 | ~spl3_56)),
% 0.20/0.47    inference(subsumption_resolution,[],[f376,f336])).
% 0.20/0.47  fof(f336,plain,(
% 0.20/0.47    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_48),
% 0.20/0.47    inference(avatar_component_clause,[],[f335])).
% 0.20/0.47  fof(f376,plain,(
% 0.20/0.47    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_55 | ~spl3_56)),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f375])).
% 0.20/0.47  fof(f375,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_55 | ~spl3_56)),
% 0.20/0.47    inference(superposition,[],[f369,f373])).
% 0.20/0.47  fof(f373,plain,(
% 0.20/0.47    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_56),
% 0.20/0.47    inference(avatar_component_clause,[],[f372])).
% 0.20/0.47  fof(f369,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_tops_2(X0,X1,X2) = k2_funct_1(X2)) ) | ~spl3_55),
% 0.20/0.47    inference(avatar_component_clause,[],[f368])).
% 0.20/0.47  fof(f350,plain,(
% 0.20/0.47    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | spl3_50),
% 0.20/0.47    inference(avatar_component_clause,[],[f349])).
% 0.20/0.47  fof(f386,plain,(
% 0.20/0.47    ~spl3_57 | ~spl3_1 | ~spl3_2 | ~spl3_48 | ~spl3_49 | spl3_52 | ~spl3_55 | ~spl3_56),
% 0.20/0.47    inference(avatar_split_clause,[],[f381,f372,f368,f357,f340,f335,f72,f68,f384])).
% 0.20/0.47  fof(f357,plain,(
% 0.20/0.47    spl3_52 <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.20/0.47  fof(f381,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_48 | ~spl3_49 | spl3_52 | ~spl3_55 | ~spl3_56)),
% 0.20/0.47    inference(backward_demodulation,[],[f358,f380])).
% 0.20/0.47  fof(f358,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | spl3_52),
% 0.20/0.47    inference(avatar_component_clause,[],[f357])).
% 0.20/0.47  fof(f374,plain,(
% 0.20/0.47    spl3_56 | ~spl3_36 | ~spl3_47),
% 0.20/0.47    inference(avatar_split_clause,[],[f322,f294,f234,f372])).
% 0.20/0.47  fof(f234,plain,(
% 0.20/0.47    spl3_36 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.20/0.47  fof(f322,plain,(
% 0.20/0.47    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_36 | ~spl3_47)),
% 0.20/0.47    inference(backward_demodulation,[],[f235,f295])).
% 0.20/0.47  fof(f235,plain,(
% 0.20/0.47    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_36),
% 0.20/0.47    inference(avatar_component_clause,[],[f234])).
% 0.20/0.47  fof(f370,plain,(
% 0.20/0.47    spl3_55),
% 0.20/0.47    inference(avatar_split_clause,[],[f61,f368])).
% 0.20/0.47  fof(f61,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_tops_2(X0,X1,X2) = k2_funct_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f33])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.47    inference(flattening,[],[f32])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f13])).
% 0.20/0.47  fof(f13,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.20/0.47  fof(f359,plain,(
% 0.20/0.47    ~spl3_52 | spl3_35 | ~spl3_47),
% 0.20/0.47    inference(avatar_split_clause,[],[f321,f294,f230,f357])).
% 0.20/0.47  fof(f230,plain,(
% 0.20/0.47    spl3_35 <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.20/0.47  fof(f321,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | (spl3_35 | ~spl3_47)),
% 0.20/0.47    inference(backward_demodulation,[],[f231,f295])).
% 0.20/0.47  fof(f231,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | spl3_35),
% 0.20/0.47    inference(avatar_component_clause,[],[f230])).
% 0.20/0.47  fof(f351,plain,(
% 0.20/0.47    ~spl3_50 | spl3_33 | ~spl3_47),
% 0.20/0.47    inference(avatar_split_clause,[],[f320,f294,f222,f349])).
% 0.20/0.47  fof(f222,plain,(
% 0.20/0.47    spl3_33 <=> k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.20/0.47  % (21132)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.20/0.47  fof(f320,plain,(
% 0.20/0.47    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | (spl3_33 | ~spl3_47)),
% 0.20/0.47    inference(backward_demodulation,[],[f223,f295])).
% 0.20/0.47  fof(f223,plain,(
% 0.20/0.47    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | spl3_33),
% 0.20/0.47    inference(avatar_component_clause,[],[f222])).
% 0.20/0.47  fof(f342,plain,(
% 0.20/0.47    spl3_49 | ~spl3_31 | ~spl3_47),
% 0.20/0.47    inference(avatar_split_clause,[],[f319,f294,f212,f340])).
% 0.20/0.47  fof(f212,plain,(
% 0.20/0.47    spl3_31 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.20/0.47  fof(f319,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_31 | ~spl3_47)),
% 0.20/0.47    inference(backward_demodulation,[],[f213,f295])).
% 0.20/0.47  fof(f213,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_31),
% 0.20/0.47    inference(avatar_component_clause,[],[f212])).
% 0.20/0.47  fof(f337,plain,(
% 0.20/0.47    spl3_48 | ~spl3_30 | ~spl3_47),
% 0.20/0.47    inference(avatar_split_clause,[],[f318,f294,f208,f335])).
% 0.20/0.47  fof(f208,plain,(
% 0.20/0.47    spl3_30 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.20/0.47  fof(f318,plain,(
% 0.20/0.47    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_30 | ~spl3_47)),
% 0.20/0.47    inference(backward_demodulation,[],[f209,f295])).
% 0.20/0.47  fof(f209,plain,(
% 0.20/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_30),
% 0.20/0.47    inference(avatar_component_clause,[],[f208])).
% 0.20/0.47  fof(f316,plain,(
% 0.20/0.47    ~spl3_7 | spl3_32 | ~spl3_46),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f315])).
% 0.20/0.47  fof(f315,plain,(
% 0.20/0.47    $false | (~spl3_7 | spl3_32 | ~spl3_46)),
% 0.20/0.47    inference(subsumption_resolution,[],[f300,f93])).
% 0.20/0.47  fof(f93,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0) | ~spl3_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f92])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    spl3_7 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.47  fof(f300,plain,(
% 0.20/0.47    ~v1_xboole_0(k1_xboole_0) | (spl3_32 | ~spl3_46)),
% 0.20/0.47    inference(backward_demodulation,[],[f217,f292])).
% 0.20/0.47  fof(f292,plain,(
% 0.20/0.47    k1_xboole_0 = k2_relat_1(sK2) | ~spl3_46),
% 0.20/0.47    inference(avatar_component_clause,[],[f291])).
% 0.20/0.47  fof(f291,plain,(
% 0.20/0.47    spl3_46 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.20/0.47  fof(f217,plain,(
% 0.20/0.47    ~v1_xboole_0(k2_relat_1(sK2)) | spl3_32),
% 0.20/0.47    inference(avatar_component_clause,[],[f216])).
% 0.20/0.47  fof(f216,plain,(
% 0.20/0.47    spl3_32 <=> v1_xboole_0(k2_relat_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.20/0.47  fof(f296,plain,(
% 0.20/0.47    spl3_46 | spl3_47 | ~spl3_30 | ~spl3_31 | ~spl3_40 | ~spl3_45),
% 0.20/0.47    inference(avatar_split_clause,[],[f289,f276,f250,f212,f208,f294,f291])).
% 0.20/0.47  fof(f250,plain,(
% 0.20/0.47    spl3_40 <=> k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.20/0.47  fof(f276,plain,(
% 0.20/0.47    spl3_45 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.20/0.47  fof(f289,plain,(
% 0.20/0.47    k2_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2) | (~spl3_30 | ~spl3_31 | ~spl3_40 | ~spl3_45)),
% 0.20/0.47    inference(forward_demodulation,[],[f288,f251])).
% 0.20/0.47  fof(f251,plain,(
% 0.20/0.47    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_40),
% 0.20/0.47    inference(avatar_component_clause,[],[f250])).
% 0.20/0.47  fof(f288,plain,(
% 0.20/0.47    k1_xboole_0 = k2_relat_1(sK2) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_30 | ~spl3_31 | ~spl3_45)),
% 0.20/0.47    inference(subsumption_resolution,[],[f285,f213])).
% 0.20/0.47  fof(f285,plain,(
% 0.20/0.47    k1_xboole_0 = k2_relat_1(sK2) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_30 | ~spl3_45)),
% 0.20/0.47    inference(resolution,[],[f277,f209])).
% 0.20/0.47  fof(f277,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_45),
% 0.20/0.47    inference(avatar_component_clause,[],[f276])).
% 0.20/0.47  fof(f278,plain,(
% 0.20/0.47    spl3_45),
% 0.20/0.47    inference(avatar_split_clause,[],[f60,f276])).
% 0.20/0.47  fof(f60,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f31])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(flattening,[],[f30])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.47  fof(f274,plain,(
% 0.20/0.47    spl3_44 | ~spl3_24 | ~spl3_31 | ~spl3_42),
% 0.20/0.47    inference(avatar_split_clause,[],[f266,f259,f212,f171,f272])).
% 0.20/0.47  fof(f171,plain,(
% 0.20/0.47    spl3_24 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k3_relset_1(X0,X1,X2) = k4_relat_1(X2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.47  fof(f259,plain,(
% 0.20/0.47    spl3_42 <=> m1_subset_1(k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.20/0.47  fof(f266,plain,(
% 0.20/0.47    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | (~spl3_24 | ~spl3_31 | ~spl3_42)),
% 0.20/0.47    inference(subsumption_resolution,[],[f265,f213])).
% 0.20/0.47  fof(f265,plain,(
% 0.20/0.47    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_24 | ~spl3_42)),
% 0.20/0.47    inference(superposition,[],[f260,f172])).
% 0.20/0.47  fof(f172,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k3_relset_1(X0,X1,X2) = k4_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_24),
% 0.20/0.47    inference(avatar_component_clause,[],[f171])).
% 0.20/0.47  fof(f260,plain,(
% 0.20/0.47    m1_subset_1(k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~spl3_42),
% 0.20/0.47    inference(avatar_component_clause,[],[f259])).
% 0.20/0.47  fof(f261,plain,(
% 0.20/0.47    spl3_42 | ~spl3_31 | ~spl3_37),
% 0.20/0.47    inference(avatar_split_clause,[],[f257,f238,f212,f259])).
% 0.20/0.47  fof(f238,plain,(
% 0.20/0.47    spl3_37 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.20/0.47  fof(f257,plain,(
% 0.20/0.47    m1_subset_1(k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | (~spl3_31 | ~spl3_37)),
% 0.20/0.47    inference(resolution,[],[f239,f213])).
% 0.20/0.47  fof(f239,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | ~spl3_37),
% 0.20/0.47    inference(avatar_component_clause,[],[f238])).
% 0.20/0.47  fof(f252,plain,(
% 0.20/0.47    spl3_40 | ~spl3_16 | ~spl3_17 | ~spl3_26 | ~spl3_28),
% 0.20/0.47    inference(avatar_split_clause,[],[f198,f188,f179,f144,f140,f250])).
% 0.20/0.47  fof(f140,plain,(
% 0.20/0.47    spl3_16 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.47  fof(f144,plain,(
% 0.20/0.47    spl3_17 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.47  fof(f188,plain,(
% 0.20/0.47    spl3_28 <=> k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.20/0.47  fof(f198,plain,(
% 0.20/0.47    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_16 | ~spl3_17 | ~spl3_26 | ~spl3_28)),
% 0.20/0.47    inference(backward_demodulation,[],[f189,f192])).
% 0.20/0.47  fof(f192,plain,(
% 0.20/0.47    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_16 | ~spl3_17 | ~spl3_26)),
% 0.20/0.47    inference(backward_demodulation,[],[f145,f191])).
% 0.20/0.47  fof(f191,plain,(
% 0.20/0.47    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | (~spl3_16 | ~spl3_26)),
% 0.20/0.47    inference(resolution,[],[f180,f141])).
% 0.20/0.47  fof(f141,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_16),
% 0.20/0.47    inference(avatar_component_clause,[],[f140])).
% 0.20/0.47  fof(f145,plain,(
% 0.20/0.47    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_17),
% 0.20/0.47    inference(avatar_component_clause,[],[f144])).
% 0.20/0.47  fof(f189,plain,(
% 0.20/0.47    k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) | ~spl3_28),
% 0.20/0.47    inference(avatar_component_clause,[],[f188])).
% 0.20/0.47  fof(f240,plain,(
% 0.20/0.47    spl3_37),
% 0.20/0.47    inference(avatar_split_clause,[],[f54,f238])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f29])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k3_relset_1)).
% 0.20/0.47  fof(f236,plain,(
% 0.20/0.47    spl3_36 | ~spl3_16 | ~spl3_17 | ~spl3_26),
% 0.20/0.47    inference(avatar_split_clause,[],[f199,f179,f144,f140,f234])).
% 0.20/0.47  fof(f199,plain,(
% 0.20/0.47    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_16 | ~spl3_17 | ~spl3_26)),
% 0.20/0.47    inference(backward_demodulation,[],[f191,f192])).
% 0.20/0.47  fof(f232,plain,(
% 0.20/0.47    ~spl3_35 | ~spl3_16 | ~spl3_17 | spl3_20 | ~spl3_26),
% 0.20/0.47    inference(avatar_split_clause,[],[f197,f179,f155,f144,f140,f230])).
% 0.20/0.47  fof(f155,plain,(
% 0.20/0.47    spl3_20 <=> k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.47  fof(f197,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | (~spl3_16 | ~spl3_17 | spl3_20 | ~spl3_26)),
% 0.20/0.47    inference(backward_demodulation,[],[f156,f192])).
% 0.20/0.47  fof(f156,plain,(
% 0.20/0.47    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl3_20),
% 0.20/0.47    inference(avatar_component_clause,[],[f155])).
% 0.20/0.47  fof(f224,plain,(
% 0.20/0.47    ~spl3_33 | ~spl3_16 | ~spl3_17 | spl3_19 | ~spl3_26),
% 0.20/0.47    inference(avatar_split_clause,[],[f196,f179,f152,f144,f140,f222])).
% 0.20/0.47  fof(f152,plain,(
% 0.20/0.47    spl3_19 <=> k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.47  fof(f196,plain,(
% 0.20/0.47    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | (~spl3_16 | ~spl3_17 | spl3_19 | ~spl3_26)),
% 0.20/0.47    inference(backward_demodulation,[],[f153,f192])).
% 0.20/0.47  fof(f153,plain,(
% 0.20/0.47    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl3_19),
% 0.20/0.47    inference(avatar_component_clause,[],[f152])).
% 0.20/0.47  fof(f218,plain,(
% 0.20/0.47    ~spl3_32 | spl3_3 | ~spl3_4 | ~spl3_12 | ~spl3_29),
% 0.20/0.47    inference(avatar_split_clause,[],[f206,f201,f112,f80,f76,f216])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    spl3_3 <=> v2_struct_0(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    spl3_4 <=> l1_struct_0(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    spl3_12 <=> ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(k2_struct_0(X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.47  fof(f201,plain,(
% 0.20/0.47    spl3_29 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.20/0.47  fof(f206,plain,(
% 0.20/0.47    ~v1_xboole_0(k2_relat_1(sK2)) | (spl3_3 | ~spl3_4 | ~spl3_12 | ~spl3_29)),
% 0.20/0.47    inference(subsumption_resolution,[],[f205,f77])).
% 0.20/0.47  fof(f77,plain,(
% 0.20/0.47    ~v2_struct_0(sK1) | spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f76])).
% 0.20/0.47  fof(f205,plain,(
% 0.20/0.47    ~v1_xboole_0(k2_relat_1(sK2)) | v2_struct_0(sK1) | (~spl3_4 | ~spl3_12 | ~spl3_29)),
% 0.20/0.47    inference(subsumption_resolution,[],[f204,f81])).
% 0.20/0.47  fof(f81,plain,(
% 0.20/0.47    l1_struct_0(sK1) | ~spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f80])).
% 0.20/0.47  fof(f204,plain,(
% 0.20/0.47    ~v1_xboole_0(k2_relat_1(sK2)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | (~spl3_12 | ~spl3_29)),
% 0.20/0.47    inference(superposition,[],[f113,f202])).
% 0.20/0.47  fof(f202,plain,(
% 0.20/0.47    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_29),
% 0.20/0.47    inference(avatar_component_clause,[],[f201])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl3_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f112])).
% 0.20/0.47  fof(f214,plain,(
% 0.20/0.47    spl3_31 | ~spl3_16 | ~spl3_17 | ~spl3_26),
% 0.20/0.47    inference(avatar_split_clause,[],[f195,f179,f144,f140,f212])).
% 0.20/0.47  fof(f195,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_16 | ~spl3_17 | ~spl3_26)),
% 0.20/0.47    inference(backward_demodulation,[],[f141,f192])).
% 0.20/0.47  fof(f210,plain,(
% 0.20/0.47    spl3_30 | ~spl3_14 | ~spl3_16 | ~spl3_17 | ~spl3_26),
% 0.20/0.47    inference(avatar_split_clause,[],[f193,f179,f144,f140,f132,f208])).
% 0.20/0.47  fof(f132,plain,(
% 0.20/0.47    spl3_14 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.47  fof(f193,plain,(
% 0.20/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_14 | ~spl3_16 | ~spl3_17 | ~spl3_26)),
% 0.20/0.47    inference(backward_demodulation,[],[f133,f192])).
% 0.20/0.47  fof(f133,plain,(
% 0.20/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_14),
% 0.20/0.47    inference(avatar_component_clause,[],[f132])).
% 0.20/0.47  fof(f203,plain,(
% 0.20/0.47    spl3_29 | ~spl3_16 | ~spl3_17 | ~spl3_26),
% 0.20/0.47    inference(avatar_split_clause,[],[f192,f179,f144,f140,f201])).
% 0.20/0.47  fof(f190,plain,(
% 0.20/0.47    spl3_28 | ~spl3_16 | ~spl3_25),
% 0.20/0.47    inference(avatar_split_clause,[],[f186,f175,f140,f188])).
% 0.20/0.47  fof(f186,plain,(
% 0.20/0.47    k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) | (~spl3_16 | ~spl3_25)),
% 0.20/0.47    inference(resolution,[],[f176,f141])).
% 0.20/0.47  fof(f181,plain,(
% 0.20/0.47    spl3_26),
% 0.20/0.47    inference(avatar_split_clause,[],[f53,f179])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    spl3_25),
% 0.20/0.47    inference(avatar_split_clause,[],[f52,f175])).
% 0.20/0.47  fof(f52,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.47  fof(f173,plain,(
% 0.20/0.47    spl3_24),
% 0.20/0.47    inference(avatar_split_clause,[],[f51,f171])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k3_relset_1(X0,X1,X2) = k4_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k3_relset_1(X0,X1,X2) = k4_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k3_relset_1(X0,X1,X2) = k4_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k3_relset_1)).
% 0.20/0.47  fof(f169,plain,(
% 0.20/0.47    spl3_23),
% 0.20/0.47    inference(avatar_split_clause,[],[f49,f167])).
% 0.20/0.47  fof(f49,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.47  fof(f165,plain,(
% 0.20/0.47    spl3_22),
% 0.20/0.47    inference(avatar_split_clause,[],[f48,f163])).
% 0.20/0.47  fof(f48,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f25])).
% 0.20/0.47  fof(f161,plain,(
% 0.20/0.47    spl3_21),
% 0.20/0.47    inference(avatar_split_clause,[],[f47,f159])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_funct_1(X0) = k4_relat_1(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0] : ((k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(X0) = k4_relat_1(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.20/0.47  fof(f157,plain,(
% 0.20/0.47    ~spl3_19 | ~spl3_20 | ~spl3_4 | ~spl3_5 | ~spl3_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f130,f108,f84,f80,f155,f152])).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    spl3_5 <=> l1_struct_0(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    spl3_11 <=> ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.47  fof(f130,plain,(
% 0.20/0.47    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_11)),
% 0.20/0.47    inference(forward_demodulation,[],[f126,f120])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    u1_struct_0(sK0) = k2_struct_0(sK0) | (~spl3_5 | ~spl3_11)),
% 0.20/0.47    inference(resolution,[],[f109,f85])).
% 0.20/0.47  fof(f85,plain,(
% 0.20/0.47    l1_struct_0(sK0) | ~spl3_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f84])).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl3_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f108])).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_11)),
% 0.20/0.47    inference(backward_demodulation,[],[f125,f120])).
% 0.20/0.47  fof(f125,plain,(
% 0.20/0.47    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_4 | ~spl3_11)),
% 0.20/0.47    inference(forward_demodulation,[],[f124,f119])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    k2_struct_0(sK1) = u1_struct_0(sK1) | (~spl3_4 | ~spl3_11)),
% 0.20/0.47    inference(resolution,[],[f109,f81])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | (~spl3_4 | ~spl3_11)),
% 0.20/0.47    inference(backward_demodulation,[],[f34,f119])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,negated_conjecture,(
% 0.20/0.47    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.20/0.47    inference(negated_conjecture,[],[f14])).
% 0.20/0.47  fof(f14,conjecture,(
% 0.20/0.47    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.20/0.47    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).
% 0.20/0.47  fof(f146,plain,(
% 0.20/0.47    spl3_17 | ~spl3_4 | ~spl3_5 | ~spl3_9 | ~spl3_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f129,f108,f100,f84,f80,f144])).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    spl3_9 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.47  fof(f129,plain,(
% 0.20/0.47    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_5 | ~spl3_9 | ~spl3_11)),
% 0.20/0.47    inference(backward_demodulation,[],[f121,f120])).
% 0.20/0.47  fof(f121,plain,(
% 0.20/0.47    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_9 | ~spl3_11)),
% 0.20/0.47    inference(backward_demodulation,[],[f101,f119])).
% 0.20/0.47  fof(f101,plain,(
% 0.20/0.47    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f100])).
% 0.20/0.47  fof(f142,plain,(
% 0.20/0.47    spl3_16 | ~spl3_4 | ~spl3_5 | ~spl3_8 | ~spl3_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f128,f108,f96,f84,f80,f140])).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    spl3_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_5 | ~spl3_8 | ~spl3_11)),
% 0.20/0.47    inference(backward_demodulation,[],[f122,f120])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_8 | ~spl3_11)),
% 0.20/0.47    inference(backward_demodulation,[],[f97,f119])).
% 0.20/0.47  fof(f97,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f96])).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    spl3_14 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f127,f108,f88,f84,f80,f132])).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    spl3_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_11)),
% 0.20/0.47    inference(backward_demodulation,[],[f123,f120])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_4 | ~spl3_6 | ~spl3_11)),
% 0.20/0.47    inference(backward_demodulation,[],[f89,f119])).
% 0.20/0.47  fof(f89,plain,(
% 0.20/0.47    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f88])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    spl3_13),
% 0.20/0.47    inference(avatar_split_clause,[],[f45,f116])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.48  fof(f19,plain,(
% 0.20/0.48    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f2])).
% 0.20/0.48  fof(f2,axiom,(
% 0.20/0.48    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.20/0.48  fof(f114,plain,(
% 0.20/0.48    spl3_12),
% 0.20/0.48    inference(avatar_split_clause,[],[f46,f112])).
% 0.20/0.48  fof(f46,plain,(
% 0.20/0.48    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(k2_struct_0(X0))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f21])).
% 0.20/0.48  fof(f21,plain,(
% 0.20/0.48    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.48    inference(flattening,[],[f20])).
% 0.20/0.48  fof(f20,plain,(
% 0.20/0.48    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.48    inference(ennf_transformation,[],[f12])).
% 0.20/0.48  fof(f12,axiom,(
% 0.20/0.48    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.20/0.48  fof(f110,plain,(
% 0.20/0.48    spl3_11),
% 0.20/0.48    inference(avatar_split_clause,[],[f44,f108])).
% 0.20/0.48  fof(f44,plain,(
% 0.20/0.48    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.48    inference(cnf_transformation,[],[f18])).
% 0.20/0.48  fof(f18,plain,(
% 0.20/0.48    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.48    inference(ennf_transformation,[],[f11])).
% 0.20/0.48  fof(f11,axiom,(
% 0.20/0.48    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.48  fof(f106,plain,(
% 0.20/0.48    spl3_10),
% 0.20/0.48    inference(avatar_split_clause,[],[f50,f104])).
% 0.20/0.48  fof(f50,plain,(
% 0.20/0.48    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.20/0.48    inference(cnf_transformation,[],[f3])).
% 0.20/0.48  fof(f3,axiom,(
% 0.20/0.48    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.20/0.48  fof(f102,plain,(
% 0.20/0.48    spl3_9),
% 0.20/0.48    inference(avatar_split_clause,[],[f38,f100])).
% 0.20/0.48  fof(f38,plain,(
% 0.20/0.48    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f98,plain,(
% 0.20/0.48    spl3_8),
% 0.20/0.48    inference(avatar_split_clause,[],[f37,f96])).
% 0.20/0.48  fof(f37,plain,(
% 0.20/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f94,plain,(
% 0.20/0.48    spl3_7),
% 0.20/0.48    inference(avatar_split_clause,[],[f43,f92])).
% 0.20/0.48  fof(f43,plain,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    inference(cnf_transformation,[],[f1])).
% 0.20/0.48  fof(f1,axiom,(
% 0.20/0.48    v1_xboole_0(k1_xboole_0)),
% 0.20/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.48  fof(f90,plain,(
% 0.20/0.48    spl3_6),
% 0.20/0.48    inference(avatar_split_clause,[],[f36,f88])).
% 0.20/0.48  fof(f36,plain,(
% 0.20/0.48    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f86,plain,(
% 0.20/0.48    spl3_5),
% 0.20/0.48    inference(avatar_split_clause,[],[f42,f84])).
% 0.20/0.48  fof(f42,plain,(
% 0.20/0.48    l1_struct_0(sK0)),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f82,plain,(
% 0.20/0.48    spl3_4),
% 0.20/0.48    inference(avatar_split_clause,[],[f41,f80])).
% 0.20/0.48  fof(f41,plain,(
% 0.20/0.48    l1_struct_0(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f78,plain,(
% 0.20/0.48    ~spl3_3),
% 0.20/0.48    inference(avatar_split_clause,[],[f40,f76])).
% 0.20/0.48  fof(f40,plain,(
% 0.20/0.48    ~v2_struct_0(sK1)),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f74,plain,(
% 0.20/0.48    spl3_2),
% 0.20/0.48    inference(avatar_split_clause,[],[f39,f72])).
% 0.20/0.48  fof(f39,plain,(
% 0.20/0.48    v2_funct_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  fof(f70,plain,(
% 0.20/0.48    spl3_1),
% 0.20/0.48    inference(avatar_split_clause,[],[f35,f68])).
% 0.20/0.48  fof(f35,plain,(
% 0.20/0.48    v1_funct_1(sK2)),
% 0.20/0.48    inference(cnf_transformation,[],[f17])).
% 0.20/0.48  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (21136)------------------------------
% 0.20/0.48  % (21136)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (21136)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (21136)Memory used [KB]: 11001
% 0.20/0.48  % (21136)Time elapsed: 0.071 s
% 0.20/0.48  % (21136)------------------------------
% 0.20/0.48  % (21136)------------------------------
% 0.20/0.48  % (21126)Success in time 0.128 s
%------------------------------------------------------------------------------
