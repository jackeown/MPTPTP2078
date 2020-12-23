%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:02:19 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  277 ( 590 expanded)
%              Number of leaves         :   64 ( 285 expanded)
%              Depth                    :    8
%              Number of atoms          :  946 (1903 expanded)
%              Number of equality atoms :  145 ( 389 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    5 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f917,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f85,f89,f93,f97,f101,f105,f139,f143,f169,f182,f186,f200,f206,f213,f217,f225,f239,f243,f247,f251,f257,f265,f271,f285,f289,f301,f305,f320,f324,f328,f335,f349,f356,f371,f389,f400,f414,f418,f422,f445,f468,f497,f530,f572,f573,f628,f729,f769,f775,f796,f814,f815,f828,f902,f915])).

fof(f915,plain,
    ( ~ spl5_87
    | ~ spl5_101 ),
    inference(avatar_contradiction_clause,[],[f909])).

fof(f909,plain,
    ( $false
    | ~ spl5_87
    | ~ spl5_101 ),
    inference(unit_resulting_resolution,[],[f728,f901])).

fof(f901,plain,
    ( ! [X0] : ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl5_101 ),
    inference(avatar_component_clause,[],[f900])).

fof(f900,plain,
    ( spl5_101
  <=> ! [X0] : ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_101])])).

fof(f728,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl5_87 ),
    inference(avatar_component_clause,[],[f727])).

fof(f727,plain,
    ( spl5_87
  <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).

fof(f902,plain,
    ( spl5_101
    | ~ spl5_72
    | ~ spl5_97 ),
    inference(avatar_split_clause,[],[f845,f791,f568,f900])).

fof(f568,plain,
    ( spl5_72
  <=> k1_xboole_0 = sK2 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).

fof(f791,plain,
    ( spl5_97
  <=> ! [X0] : ~ v1_funct_2(sK2,k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).

fof(f845,plain,
    ( ! [X0] : ~ v1_funct_2(k1_xboole_0,k1_xboole_0,X0)
    | ~ spl5_72
    | ~ spl5_97 ),
    inference(backward_demodulation,[],[f792,f569])).

fof(f569,plain,
    ( k1_xboole_0 = sK2
    | ~ spl5_72 ),
    inference(avatar_component_clause,[],[f568])).

fof(f792,plain,
    ( ! [X0] : ~ v1_funct_2(sK2,k1_xboole_0,X0)
    | ~ spl5_97 ),
    inference(avatar_component_clause,[],[f791])).

fof(f828,plain,
    ( spl5_14
    | ~ spl5_55
    | ~ spl5_66
    | ~ spl5_94
    | ~ spl5_98 ),
    inference(avatar_contradiction_clause,[],[f827])).

fof(f827,plain,
    ( $false
    | spl5_14
    | ~ spl5_55
    | ~ spl5_66
    | ~ spl5_94
    | ~ spl5_98 ),
    inference(subsumption_resolution,[],[f798,f824])).

fof(f824,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)
    | spl5_14
    | ~ spl5_55
    | ~ spl5_66 ),
    inference(forward_demodulation,[],[f823,f437])).

fof(f437,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_66 ),
    inference(avatar_component_clause,[],[f436])).

fof(f436,plain,
    ( spl5_66
  <=> k1_xboole_0 = sK1 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).

fof(f823,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,k1_xboole_0)
    | spl5_14
    | ~ spl5_55 ),
    inference(forward_demodulation,[],[f135,f355])).

fof(f355,plain,
    ( k1_xboole_0 = sK0
    | ~ spl5_55 ),
    inference(avatar_component_clause,[],[f354])).

fof(f354,plain,
    ( spl5_55
  <=> k1_xboole_0 = sK0 ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).

fof(f135,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | spl5_14 ),
    inference(avatar_component_clause,[],[f134])).

fof(f134,plain,
    ( spl5_14
  <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).

fof(f798,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0)
    | ~ spl5_94
    | ~ spl5_98 ),
    inference(backward_demodulation,[],[f774,f795])).

fof(f795,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl5_98 ),
    inference(avatar_component_clause,[],[f794])).

fof(f794,plain,
    ( spl5_98
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).

fof(f774,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_relat_1(sK2))
    | ~ spl5_94 ),
    inference(avatar_component_clause,[],[f773])).

fof(f773,plain,
    ( spl5_94
  <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).

fof(f815,plain,
    ( ~ spl5_61
    | ~ spl5_15
    | spl5_13
    | ~ spl5_36
    | ~ spl5_37
    | ~ spl5_44
    | ~ spl5_47
    | ~ spl5_52
    | ~ spl5_70 ),
    inference(avatar_split_clause,[],[f598,f528,f333,f299,f283,f241,f237,f131,f137,f395])).

fof(f395,plain,
    ( spl5_61
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).

fof(f137,plain,
    ( spl5_15
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).

fof(f131,plain,
    ( spl5_13
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).

fof(f237,plain,
    ( spl5_36
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).

fof(f241,plain,
    ( spl5_37
  <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).

fof(f283,plain,
    ( spl5_44
  <=> sK1 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).

fof(f299,plain,
    ( spl5_47
  <=> sK1 = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).

fof(f333,plain,
    ( spl5_52
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).

fof(f528,plain,
    ( spl5_70
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).

fof(f598,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | spl5_13
    | ~ spl5_36
    | ~ spl5_37
    | ~ spl5_44
    | ~ spl5_47
    | ~ spl5_52
    | ~ spl5_70 ),
    inference(subsumption_resolution,[],[f597,f595])).

fof(f595,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | spl5_13
    | ~ spl5_37
    | ~ spl5_44
    | ~ spl5_70 ),
    inference(forward_demodulation,[],[f581,f242])).

fof(f242,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)
    | ~ spl5_37 ),
    inference(avatar_component_clause,[],[f241])).

fof(f581,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0)))
    | spl5_13
    | ~ spl5_44
    | ~ spl5_70 ),
    inference(backward_demodulation,[],[f132,f577])).

fof(f577,plain,
    ( k1_xboole_0 = sK1
    | ~ spl5_44
    | ~ spl5_70 ),
    inference(backward_demodulation,[],[f284,f529])).

fof(f529,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl5_70 ),
    inference(avatar_component_clause,[],[f528])).

fof(f284,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl5_44 ),
    inference(avatar_component_clause,[],[f283])).

fof(f132,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl5_13 ),
    inference(avatar_component_clause,[],[f131])).

fof(f597,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_36
    | ~ spl5_37
    | ~ spl5_44
    | ~ spl5_47
    | ~ spl5_52
    | ~ spl5_70 ),
    inference(forward_demodulation,[],[f588,f242])).

fof(f588,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_36
    | ~ spl5_44
    | ~ spl5_47
    | ~ spl5_52
    | ~ spl5_70 ),
    inference(backward_demodulation,[],[f499,f577])).

fof(f499,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_36
    | ~ spl5_47
    | ~ spl5_52 ),
    inference(backward_demodulation,[],[f492,f334])).

fof(f334,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_52 ),
    inference(avatar_component_clause,[],[f333])).

fof(f492,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_36
    | ~ spl5_47 ),
    inference(superposition,[],[f238,f300])).

fof(f300,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_47 ),
    inference(avatar_component_clause,[],[f299])).

fof(f238,plain,
    ( ! [X0] :
        ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_36 ),
    inference(avatar_component_clause,[],[f237])).

fof(f814,plain,
    ( spl5_72
    | spl5_98
    | ~ spl5_44
    | ~ spl5_45
    | ~ spl5_53
    | ~ spl5_70
    | ~ spl5_93 ),
    inference(avatar_split_clause,[],[f771,f767,f528,f347,f287,f283,f794,f568])).

fof(f287,plain,
    ( spl5_45
  <=> ! [X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X2
        | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).

fof(f347,plain,
    ( spl5_53
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).

fof(f767,plain,
    ( spl5_93
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).

fof(f771,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ spl5_44
    | ~ spl5_45
    | ~ spl5_53
    | ~ spl5_70
    | ~ spl5_93 ),
    inference(subsumption_resolution,[],[f770,f585])).

fof(f585,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))
    | ~ spl5_44
    | ~ spl5_53
    | ~ spl5_70 ),
    inference(backward_demodulation,[],[f348,f577])).

fof(f348,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ spl5_53 ),
    inference(avatar_component_clause,[],[f347])).

fof(f770,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k1_xboole_0 = sK2
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0)))
    | ~ spl5_45
    | ~ spl5_93 ),
    inference(resolution,[],[f768,f288])).

fof(f288,plain,
    ( ! [X2,X0] :
        ( ~ v1_funct_2(X2,X0,k1_xboole_0)
        | k1_xboole_0 = X0
        | k1_xboole_0 = X2
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) )
    | ~ spl5_45 ),
    inference(avatar_component_clause,[],[f287])).

fof(f768,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | ~ spl5_93 ),
    inference(avatar_component_clause,[],[f767])).

fof(f796,plain,
    ( spl5_97
    | spl5_98
    | ~ spl5_60
    | ~ spl5_63 ),
    inference(avatar_split_clause,[],[f724,f412,f387,f794,f791])).

fof(f387,plain,
    ( spl5_60
  <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).

fof(f412,plain,
    ( spl5_63
  <=> ! [X3,X2] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k1_relat_1(X3)
        | ~ v1_funct_2(X3,k1_xboole_0,X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).

fof(f724,plain,
    ( ! [X0] :
        ( k1_xboole_0 = k1_relat_1(sK2)
        | ~ v1_funct_2(sK2,k1_xboole_0,X0) )
    | ~ spl5_60
    | ~ spl5_63 ),
    inference(resolution,[],[f388,f413])).

fof(f413,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k1_relat_1(X3)
        | ~ v1_funct_2(X3,k1_xboole_0,X2) )
    | ~ spl5_63 ),
    inference(avatar_component_clause,[],[f412])).

fof(f388,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_60 ),
    inference(avatar_component_clause,[],[f387])).

fof(f775,plain,
    ( spl5_94
    | ~ spl5_44
    | ~ spl5_62
    | ~ spl5_70 ),
    inference(avatar_split_clause,[],[f587,f528,f398,f283,f773])).

fof(f398,plain,
    ( spl5_62
  <=> v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).

fof(f587,plain,
    ( v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_relat_1(sK2))
    | ~ spl5_44
    | ~ spl5_62
    | ~ spl5_70 ),
    inference(backward_demodulation,[],[f399,f577])).

fof(f399,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ spl5_62 ),
    inference(avatar_component_clause,[],[f398])).

fof(f769,plain,
    ( spl5_93
    | ~ spl5_44
    | ~ spl5_49
    | ~ spl5_70 ),
    inference(avatar_split_clause,[],[f584,f528,f318,f283,f767])).

fof(f318,plain,
    ( spl5_49
  <=> v1_funct_2(sK2,k1_relat_1(sK2),sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).

fof(f584,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)
    | ~ spl5_44
    | ~ spl5_49
    | ~ spl5_70 ),
    inference(backward_demodulation,[],[f319,f577])).

fof(f319,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ spl5_49 ),
    inference(avatar_component_clause,[],[f318])).

fof(f729,plain,
    ( spl5_87
    | ~ spl5_55
    | ~ spl5_74 ),
    inference(avatar_split_clause,[],[f712,f626,f354,f727])).

fof(f626,plain,
    ( spl5_74
  <=> v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).

fof(f712,plain,
    ( v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)
    | ~ spl5_55
    | ~ spl5_74 ),
    inference(backward_demodulation,[],[f627,f355])).

fof(f627,plain,
    ( v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl5_74 ),
    inference(avatar_component_clause,[],[f626])).

fof(f628,plain,
    ( spl5_74
    | ~ spl5_67
    | ~ spl5_72 ),
    inference(avatar_split_clause,[],[f602,f568,f466,f626])).

fof(f466,plain,
    ( spl5_67
  <=> v1_funct_2(sK2,sK0,k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).

fof(f602,plain,
    ( v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)
    | ~ spl5_67
    | ~ spl5_72 ),
    inference(backward_demodulation,[],[f467,f569])).

fof(f467,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl5_67 ),
    inference(avatar_component_clause,[],[f466])).

fof(f573,plain,
    ( ~ spl5_61
    | ~ spl5_15
    | spl5_13
    | ~ spl5_36
    | ~ spl5_47
    | ~ spl5_52
    | ~ spl5_68 ),
    inference(avatar_split_clause,[],[f539,f495,f333,f299,f237,f131,f137,f395])).

fof(f495,plain,
    ( spl5_68
  <=> sK0 = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).

fof(f539,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | spl5_13
    | ~ spl5_36
    | ~ spl5_47
    | ~ spl5_52
    | ~ spl5_68 ),
    inference(subsumption_resolution,[],[f537,f132])).

fof(f537,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_36
    | ~ spl5_47
    | ~ spl5_52
    | ~ spl5_68 ),
    inference(backward_demodulation,[],[f499,f531])).

fof(f531,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_52
    | ~ spl5_68 ),
    inference(backward_demodulation,[],[f334,f496])).

fof(f496,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_68 ),
    inference(avatar_component_clause,[],[f495])).

fof(f572,plain,
    ( spl5_65
    | spl5_66
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_64 ),
    inference(avatar_split_clause,[],[f498,f420,f95,f91,f436,f433])).

fof(f433,plain,
    ( spl5_65
  <=> sK0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).

fof(f91,plain,
    ( spl5_3
  <=> v1_funct_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).

fof(f95,plain,
    ( spl5_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).

fof(f420,plain,
    ( spl5_64
  <=> ! [X3,X5,X4] :
        ( k1_relat_1(X5) = X3
        | k1_xboole_0 = X4
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ v1_funct_2(X5,X3,X4) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).

fof(f498,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relat_1(sK2)
    | ~ spl5_3
    | ~ spl5_4
    | ~ spl5_64 ),
    inference(subsumption_resolution,[],[f482,f92])).

fof(f92,plain,
    ( v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_3 ),
    inference(avatar_component_clause,[],[f91])).

fof(f482,plain,
    ( k1_xboole_0 = sK1
    | sK0 = k1_relat_1(sK2)
    | ~ v1_funct_2(sK2,sK0,sK1)
    | ~ spl5_4
    | ~ spl5_64 ),
    inference(resolution,[],[f96,f421])).

fof(f421,plain,
    ( ! [X4,X5,X3] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | k1_xboole_0 = X4
        | k1_relat_1(X5) = X3
        | ~ v1_funct_2(X5,X3,X4) )
    | ~ spl5_64 ),
    inference(avatar_component_clause,[],[f420])).

fof(f96,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_4 ),
    inference(avatar_component_clause,[],[f95])).

fof(f530,plain,
    ( spl5_70
    | ~ spl5_44
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f506,f436,f283,f528])).

fof(f506,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl5_44
    | ~ spl5_66 ),
    inference(backward_demodulation,[],[f284,f437])).

fof(f497,plain,
    ( spl5_68
    | ~ spl5_52
    | ~ spl5_65 ),
    inference(avatar_split_clause,[],[f473,f433,f333,f495])).

fof(f473,plain,
    ( sK0 = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_52
    | ~ spl5_65 ),
    inference(backward_demodulation,[],[f334,f434])).

fof(f434,plain,
    ( sK0 = k1_relat_1(sK2)
    | ~ spl5_65 ),
    inference(avatar_component_clause,[],[f433])).

fof(f468,plain,
    ( spl5_67
    | ~ spl5_3
    | ~ spl5_66 ),
    inference(avatar_split_clause,[],[f447,f436,f91,f466])).

fof(f447,plain,
    ( v1_funct_2(sK2,sK0,k1_xboole_0)
    | ~ spl5_3
    | ~ spl5_66 ),
    inference(backward_demodulation,[],[f92,f437])).

fof(f445,plain,
    ( spl5_14
    | ~ spl5_62
    | ~ spl5_65 ),
    inference(avatar_contradiction_clause,[],[f444])).

fof(f444,plain,
    ( $false
    | spl5_14
    | ~ spl5_62
    | ~ spl5_65 ),
    inference(subsumption_resolution,[],[f439,f135])).

fof(f439,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ spl5_62
    | ~ spl5_65 ),
    inference(backward_demodulation,[],[f399,f434])).

fof(f422,plain,
    ( spl5_64
    | ~ spl5_40
    | ~ spl5_51 ),
    inference(avatar_split_clause,[],[f341,f326,f255,f420])).

fof(f255,plain,
    ( spl5_40
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).

fof(f326,plain,
    ( spl5_51
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).

fof(f341,plain,
    ( ! [X4,X5,X3] :
        ( k1_relat_1(X5) = X3
        | k1_xboole_0 = X4
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ v1_funct_2(X5,X3,X4) )
    | ~ spl5_40
    | ~ spl5_51 ),
    inference(duplicate_literal_removal,[],[f338])).

fof(f338,plain,
    ( ! [X4,X5,X3] :
        ( k1_relat_1(X5) = X3
        | k1_xboole_0 = X4
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))
        | ~ v1_funct_2(X5,X3,X4)
        | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) )
    | ~ spl5_40
    | ~ spl5_51 ),
    inference(superposition,[],[f327,f256])).

fof(f256,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_40 ),
    inference(avatar_component_clause,[],[f255])).

fof(f327,plain,
    ( ! [X2,X0,X1] :
        ( k1_relset_1(X0,X1,X2) = X0
        | k1_xboole_0 = X1
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1) )
    | ~ spl5_51 ),
    inference(avatar_component_clause,[],[f326])).

% (21250)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
fof(f418,plain,
    ( ~ spl5_30
    | ~ spl5_1
    | ~ spl5_25
    | spl5_61 ),
    inference(avatar_split_clause,[],[f410,f395,f180,f83,f204])).

fof(f204,plain,
    ( spl5_30
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).

fof(f83,plain,
    ( spl5_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).

fof(f180,plain,
    ( spl5_25
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | v1_relat_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).

fof(f410,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl5_1
    | ~ spl5_25
    | spl5_61 ),
    inference(subsumption_resolution,[],[f408,f84])).

fof(f84,plain,
    ( v1_funct_1(sK2)
    | ~ spl5_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f408,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_25
    | spl5_61 ),
    inference(resolution,[],[f396,f181])).

fof(f181,plain,
    ( ! [X0] :
        ( v1_relat_1(k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_25 ),
    inference(avatar_component_clause,[],[f180])).

fof(f396,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl5_61 ),
    inference(avatar_component_clause,[],[f395])).

fof(f414,plain,
    ( spl5_63
    | ~ spl5_37
    | ~ spl5_40
    | ~ spl5_48 ),
    inference(avatar_split_clause,[],[f309,f303,f255,f241,f412])).

fof(f303,plain,
    ( spl5_48
  <=> ! [X1,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
        | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).

fof(f309,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k1_relat_1(X3)
        | ~ v1_funct_2(X3,k1_xboole_0,X2) )
    | ~ spl5_37
    | ~ spl5_40
    | ~ spl5_48 ),
    inference(duplicate_literal_removal,[],[f308])).

fof(f308,plain,
    ( ! [X2,X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k1_relat_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(X3,k1_xboole_0,X2) )
    | ~ spl5_37
    | ~ spl5_40
    | ~ spl5_48 ),
    inference(forward_demodulation,[],[f306,f242])).

fof(f306,plain,
    ( ! [X2,X3] :
        ( k1_xboole_0 = k1_relat_1(X3)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(X3,k1_xboole_0,X2)
        | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2))) )
    | ~ spl5_40
    | ~ spl5_48 ),
    inference(superposition,[],[f304,f256])).

% (21247)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f304,plain,
    ( ! [X2,X1] :
        ( k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | ~ v1_funct_2(X2,k1_xboole_0,X1) )
    | ~ spl5_48 ),
    inference(avatar_component_clause,[],[f303])).

fof(f400,plain,
    ( ~ spl5_61
    | ~ spl5_15
    | spl5_62
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_32
    | ~ spl5_42
    | ~ spl5_43
    | ~ spl5_52 ),
    inference(avatar_split_clause,[],[f337,f333,f269,f263,f215,f99,f95,f398,f137,f395])).

fof(f99,plain,
    ( spl5_5
  <=> sK1 = k2_relset_1(sK0,sK1,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).

fof(f215,plain,
    ( spl5_32
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).

fof(f263,plain,
    ( spl5_42
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).

fof(f269,plain,
    ( spl5_43
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).

fof(f337,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_32
    | ~ spl5_42
    | ~ spl5_43
    | ~ spl5_52 ),
    inference(backward_demodulation,[],[f279,f334])).

fof(f279,plain,
    ( v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_32
    | ~ spl5_42
    | ~ spl5_43 ),
    inference(backward_demodulation,[],[f275,f278])).

fof(f278,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_42 ),
    inference(subsumption_resolution,[],[f276,f96])).

fof(f276,plain,
    ( sK1 = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))
    | ~ spl5_5
    | ~ spl5_42 ),
    inference(superposition,[],[f264,f100])).

fof(f100,plain,
    ( sK1 = k2_relset_1(sK0,sK1,sK2)
    | ~ spl5_5 ),
    inference(avatar_component_clause,[],[f99])).

fof(f264,plain,
    ( ! [X2,X0,X1] :
        ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_42 ),
    inference(avatar_component_clause,[],[f263])).

fof(f275,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl5_32
    | ~ spl5_43 ),
    inference(superposition,[],[f216,f270])).

fof(f270,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_43 ),
    inference(avatar_component_clause,[],[f269])).

fof(f216,plain,
    ( ! [X0] :
        ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_32 ),
    inference(avatar_component_clause,[],[f215])).

fof(f389,plain,
    ( spl5_60
    | ~ spl5_4
    | ~ spl5_37
    | ~ spl5_55 ),
    inference(avatar_split_clause,[],[f376,f354,f241,f95,f387])).

fof(f376,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))
    | ~ spl5_4
    | ~ spl5_37
    | ~ spl5_55 ),
    inference(forward_demodulation,[],[f373,f242])).

fof(f373,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1)))
    | ~ spl5_4
    | ~ spl5_55 ),
    inference(backward_demodulation,[],[f96,f355])).

fof(f371,plain,
    ( ~ spl5_13
    | ~ spl5_40
    | ~ spl5_47
    | spl5_54 ),
    inference(avatar_split_clause,[],[f360,f351,f299,f255,f131])).

fof(f351,plain,
    ( spl5_54
  <=> sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).

fof(f360,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_40
    | ~ spl5_47
    | spl5_54 ),
    inference(subsumption_resolution,[],[f358,f300])).

fof(f358,plain,
    ( sK1 != k1_relat_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | ~ spl5_40
    | spl5_54 ),
    inference(superposition,[],[f352,f256])).

fof(f352,plain,
    ( sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | spl5_54 ),
    inference(avatar_component_clause,[],[f351])).

fof(f356,plain,
    ( ~ spl5_13
    | ~ spl5_54
    | spl5_55
    | spl5_14
    | ~ spl5_50 ),
    inference(avatar_split_clause,[],[f329,f322,f134,f354,f351,f131])).

fof(f322,plain,
    ( spl5_50
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) != X0
        | v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).

fof(f329,plain,
    ( k1_xboole_0 = sK0
    | sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))
    | spl5_14
    | ~ spl5_50 ),
    inference(resolution,[],[f323,f135])).

fof(f323,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(X2,X0,X1)
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) != X0
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_50 ),
    inference(avatar_component_clause,[],[f322])).

fof(f349,plain,
    ( ~ spl5_30
    | spl5_53
    | ~ spl5_1
    | ~ spl5_36
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f296,f283,f237,f83,f347,f204])).

fof(f296,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_relat_1(sK2)
    | ~ spl5_1
    | ~ spl5_36
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f294,f84])).

fof(f294,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_36
    | ~ spl5_44 ),
    inference(superposition,[],[f238,f284])).

fof(f335,plain,
    ( spl5_52
    | ~ spl5_30
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_39 ),
    inference(avatar_split_clause,[],[f273,f249,f87,f83,f204,f333])).

fof(f87,plain,
    ( spl5_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).

fof(f249,plain,
    ( spl5_39
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).

fof(f273,plain,
    ( ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_39 ),
    inference(subsumption_resolution,[],[f272,f84])).

fof(f272,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl5_2
    | ~ spl5_39 ),
    inference(resolution,[],[f250,f88])).

fof(f88,plain,
    ( v2_funct_1(sK2)
    | ~ spl5_2 ),
    inference(avatar_component_clause,[],[f87])).

fof(f250,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) )
    | ~ spl5_39 ),
    inference(avatar_component_clause,[],[f249])).

fof(f328,plain,(
    spl5_51 ),
    inference(avatar_split_clause,[],[f73,f326])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
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
    inference(flattening,[],[f33])).

fof(f33,plain,(
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
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
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

fof(f324,plain,(
    spl5_50 ),
    inference(avatar_split_clause,[],[f72,f322])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) != X0
      | v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f320,plain,
    ( ~ spl5_30
    | spl5_49
    | ~ spl5_1
    | ~ spl5_32
    | ~ spl5_44 ),
    inference(avatar_split_clause,[],[f297,f283,f215,f83,f318,f204])).

fof(f297,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ v1_relat_1(sK2)
    | ~ spl5_1
    | ~ spl5_32
    | ~ spl5_44 ),
    inference(subsumption_resolution,[],[f295,f84])).

fof(f295,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl5_32
    | ~ spl5_44 ),
    inference(superposition,[],[f216,f284])).

fof(f305,plain,
    ( spl5_48
    | ~ spl5_6
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f230,f223,f103,f303])).

fof(f103,plain,
    ( spl5_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).

fof(f223,plain,
    ( spl5_34
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).

fof(f230,plain,
    ( ! [X2,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0))
        | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
        | ~ v1_funct_2(X2,k1_xboole_0,X1) )
    | ~ spl5_6
    | ~ spl5_34 ),
    inference(backward_demodulation,[],[f76,f227])).

fof(f227,plain,
    ( ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)
    | ~ spl5_6
    | ~ spl5_34 ),
    inference(resolution,[],[f224,f104])).

fof(f104,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl5_6 ),
    inference(avatar_component_clause,[],[f103])).

fof(f224,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) )
    | ~ spl5_34 ),
    inference(avatar_component_clause,[],[f223])).

fof(f76,plain,(
    ! [X2,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1)))
      | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2)
      | ~ v1_funct_2(X2,k1_xboole_0,X1) ) ),
    inference(equality_resolution,[],[f71])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X0
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f301,plain,
    ( spl5_47
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_42
    | ~ spl5_43 ),
    inference(avatar_split_clause,[],[f281,f269,f263,f99,f95,f299])).

fof(f281,plain,
    ( sK1 = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_42
    | ~ spl5_43 ),
    inference(backward_demodulation,[],[f270,f278])).

fof(f289,plain,(
    spl5_45 ),
    inference(avatar_split_clause,[],[f78,f287])).

fof(f78,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f285,plain,
    ( spl5_44
    | ~ spl5_4
    | ~ spl5_5
    | ~ spl5_42 ),
    inference(avatar_split_clause,[],[f278,f263,f99,f95,f283])).

fof(f271,plain,
    ( spl5_43
    | ~ spl5_30
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_38 ),
    inference(avatar_split_clause,[],[f267,f245,f87,f83,f204,f269])).

fof(f245,plain,
    ( spl5_38
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).

fof(f267,plain,
    ( ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_1
    | ~ spl5_2
    | ~ spl5_38 ),
    inference(subsumption_resolution,[],[f266,f84])).

fof(f266,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl5_2
    | ~ spl5_38 ),
    inference(resolution,[],[f246,f88])).

fof(f246,plain,
    ( ! [X0] :
        ( ~ v2_funct_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
    | ~ spl5_38 ),
    inference(avatar_component_clause,[],[f245])).

fof(f265,plain,(
    spl5_42 ),
    inference(avatar_split_clause,[],[f67,f263])).

fof(f67,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f257,plain,(
    spl5_40 ),
    inference(avatar_split_clause,[],[f66,f255])).

fof(f66,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f251,plain,(
    spl5_39 ),
    inference(avatar_split_clause,[],[f55,f249])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).

fof(f247,plain,(
    spl5_38 ),
    inference(avatar_split_clause,[],[f54,f245])).

fof(f54,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f243,plain,
    ( spl5_37
    | ~ spl5_6
    | ~ spl5_34 ),
    inference(avatar_split_clause,[],[f227,f223,f103,f241])).

fof(f239,plain,(
    spl5_36 ),
    inference(avatar_split_clause,[],[f51,f237])).

fof(f51,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).

fof(f225,plain,
    ( spl5_34
    | ~ spl5_16
    | ~ spl5_22 ),
    inference(avatar_split_clause,[],[f192,f167,f141,f223])).

fof(f141,plain,
    ( spl5_16
  <=> ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).

fof(f167,plain,
    ( spl5_22
  <=> ! [X1,X0] :
        ( ~ v1_xboole_0(X0)
        | v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).

fof(f192,plain,
    ( ! [X0,X1] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = k2_zfmisc_1(X0,X1) )
    | ~ spl5_16
    | ~ spl5_22 ),
    inference(resolution,[],[f168,f142])).

fof(f142,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(X0)
        | k1_xboole_0 = X0 )
    | ~ spl5_16 ),
    inference(avatar_component_clause,[],[f141])).

fof(f168,plain,
    ( ! [X0,X1] :
        ( v1_xboole_0(k2_zfmisc_1(X0,X1))
        | ~ v1_xboole_0(X0) )
    | ~ spl5_22 ),
    inference(avatar_component_clause,[],[f167])).

fof(f217,plain,(
    spl5_32 ),
    inference(avatar_split_clause,[],[f50,f215])).

fof(f50,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f213,plain,
    ( ~ spl5_4
    | ~ spl5_29
    | spl5_30 ),
    inference(avatar_contradiction_clause,[],[f211])).

fof(f211,plain,
    ( $false
    | ~ spl5_4
    | ~ spl5_29
    | spl5_30 ),
    inference(unit_resulting_resolution,[],[f205,f96,f199])).

fof(f199,plain,
    ( ! [X2,X0,X1] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl5_29 ),
    inference(avatar_component_clause,[],[f198])).

fof(f198,plain,
    ( spl5_29
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).

fof(f205,plain,
    ( ~ v1_relat_1(sK2)
    | spl5_30 ),
    inference(avatar_component_clause,[],[f204])).

fof(f206,plain,
    ( ~ spl5_30
    | ~ spl5_1
    | spl5_15
    | ~ spl5_26 ),
    inference(avatar_split_clause,[],[f202,f184,f137,f83,f204])).

fof(f184,plain,
    ( spl5_26
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | v1_funct_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).

fof(f202,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl5_1
    | spl5_15
    | ~ spl5_26 ),
    inference(subsumption_resolution,[],[f201,f84])).

fof(f201,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl5_15
    | ~ spl5_26 ),
    inference(resolution,[],[f185,f138])).

fof(f138,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl5_15 ),
    inference(avatar_component_clause,[],[f137])).

fof(f185,plain,
    ( ! [X0] :
        ( v1_funct_1(k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl5_26 ),
    inference(avatar_component_clause,[],[f184])).

fof(f200,plain,(
    spl5_29 ),
    inference(avatar_split_clause,[],[f65,f198])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f186,plain,(
    spl5_26 ),
    inference(avatar_split_clause,[],[f53,f184])).

fof(f53,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_funct_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f182,plain,(
    spl5_25 ),
    inference(avatar_split_clause,[],[f52,f180])).

fof(f52,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | v1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f169,plain,(
    spl5_22 ),
    inference(avatar_split_clause,[],[f58,f167])).

fof(f58,plain,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X0)
      | v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1] :
      ( v1_xboole_0(k2_zfmisc_1(X0,X1))
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1] :
      ( v1_xboole_0(X0)
     => v1_xboole_0(k2_zfmisc_1(X0,X1)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).

fof(f143,plain,(
    spl5_16 ),
    inference(avatar_split_clause,[],[f49,f141])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(X0)
      | k1_xboole_0 = X0 ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( k1_xboole_0 = X0
      | ~ v1_xboole_0(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v1_xboole_0(X0)
     => k1_xboole_0 = X0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

fof(f139,plain,
    ( ~ spl5_13
    | ~ spl5_14
    | ~ spl5_15 ),
    inference(avatar_split_clause,[],[f38,f137,f134,f131])).

fof(f38,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),sK1,sK0)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ? [X0,X1,X2] :
      ( ( ~ m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(k2_funct_1(X2),X1,X0)
        | ~ v1_funct_1(k2_funct_1(X2)) )
      & k2_relset_1(X0,X1,X2) = X1
      & v2_funct_1(X2)
      & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      & v1_funct_2(X2,X0,X1)
      & v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,negated_conjecture,(
    ~ ! [X0,X1,X2] :
        ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( ( k2_relset_1(X0,X1,X2) = X1
            & v2_funct_1(X2) )
         => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
            & v1_funct_2(k2_funct_1(X2),X1,X0)
            & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    inference(negated_conjecture,[],[f18])).

fof(f18,conjecture,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).

fof(f105,plain,(
    spl5_6 ),
    inference(avatar_split_clause,[],[f44,f103])).

fof(f44,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f101,plain,(
    spl5_5 ),
    inference(avatar_split_clause,[],[f43,f99])).

fof(f43,plain,(
    sK1 = k2_relset_1(sK0,sK1,sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f97,plain,(
    spl5_4 ),
    inference(avatar_split_clause,[],[f41,f95])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) ),
    inference(cnf_transformation,[],[f21])).

fof(f93,plain,(
    spl5_3 ),
    inference(avatar_split_clause,[],[f40,f91])).

fof(f40,plain,(
    v1_funct_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f21])).

fof(f89,plain,(
    spl5_2 ),
    inference(avatar_split_clause,[],[f42,f87])).

fof(f42,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).

fof(f85,plain,(
    spl5_1 ),
    inference(avatar_split_clause,[],[f39,f83])).

fof(f39,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 19:59:07 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.44  % (21255)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.45  % (21251)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.46  % (21259)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.47  % (21245)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.47  % (21251)Refutation found. Thanks to Tanya!
% 0.21/0.47  % SZS status Theorem for theBenchmark
% 0.21/0.47  % (21245)Refutation not found, incomplete strategy% (21245)------------------------------
% 0.21/0.47  % (21245)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.47  % (21261)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.48  % (21253)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.48  % (21249)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.48  % (21246)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.48  % (21245)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.48  
% 0.21/0.48  % (21245)Memory used [KB]: 10874
% 0.21/0.48  % (21245)Time elapsed: 0.065 s
% 0.21/0.48  % (21245)------------------------------
% 0.21/0.48  % (21245)------------------------------
% 0.21/0.48  % SZS output start Proof for theBenchmark
% 0.21/0.48  fof(f917,plain,(
% 0.21/0.48    $false),
% 0.21/0.48    inference(avatar_sat_refutation,[],[f85,f89,f93,f97,f101,f105,f139,f143,f169,f182,f186,f200,f206,f213,f217,f225,f239,f243,f247,f251,f257,f265,f271,f285,f289,f301,f305,f320,f324,f328,f335,f349,f356,f371,f389,f400,f414,f418,f422,f445,f468,f497,f530,f572,f573,f628,f729,f769,f775,f796,f814,f815,f828,f902,f915])).
% 0.21/0.48  fof(f915,plain,(
% 0.21/0.48    ~spl5_87 | ~spl5_101),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f909])).
% 0.21/0.48  fof(f909,plain,(
% 0.21/0.48    $false | (~spl5_87 | ~spl5_101)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f728,f901])).
% 0.21/0.48  fof(f901,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | ~spl5_101),
% 0.21/0.48    inference(avatar_component_clause,[],[f900])).
% 0.21/0.48  fof(f900,plain,(
% 0.21/0.48    spl5_101 <=> ! [X0] : ~v1_funct_2(k1_xboole_0,k1_xboole_0,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_101])])).
% 0.21/0.48  fof(f728,plain,(
% 0.21/0.48    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | ~spl5_87),
% 0.21/0.48    inference(avatar_component_clause,[],[f727])).
% 0.21/0.48  fof(f727,plain,(
% 0.21/0.48    spl5_87 <=> v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_87])])).
% 0.21/0.48  fof(f902,plain,(
% 0.21/0.48    spl5_101 | ~spl5_72 | ~spl5_97),
% 0.21/0.48    inference(avatar_split_clause,[],[f845,f791,f568,f900])).
% 0.21/0.48  fof(f568,plain,(
% 0.21/0.48    spl5_72 <=> k1_xboole_0 = sK2),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_72])])).
% 0.21/0.48  fof(f791,plain,(
% 0.21/0.48    spl5_97 <=> ! [X0] : ~v1_funct_2(sK2,k1_xboole_0,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_97])])).
% 0.21/0.48  fof(f845,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_2(k1_xboole_0,k1_xboole_0,X0)) ) | (~spl5_72 | ~spl5_97)),
% 0.21/0.48    inference(backward_demodulation,[],[f792,f569])).
% 0.21/0.48  fof(f569,plain,(
% 0.21/0.48    k1_xboole_0 = sK2 | ~spl5_72),
% 0.21/0.48    inference(avatar_component_clause,[],[f568])).
% 0.21/0.48  fof(f792,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_funct_2(sK2,k1_xboole_0,X0)) ) | ~spl5_97),
% 0.21/0.48    inference(avatar_component_clause,[],[f791])).
% 0.21/0.48  fof(f828,plain,(
% 0.21/0.48    spl5_14 | ~spl5_55 | ~spl5_66 | ~spl5_94 | ~spl5_98),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f827])).
% 0.21/0.48  fof(f827,plain,(
% 0.21/0.48    $false | (spl5_14 | ~spl5_55 | ~spl5_66 | ~spl5_94 | ~spl5_98)),
% 0.21/0.48    inference(subsumption_resolution,[],[f798,f824])).
% 0.21/0.48  fof(f824,plain,(
% 0.21/0.48    ~v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) | (spl5_14 | ~spl5_55 | ~spl5_66)),
% 0.21/0.48    inference(forward_demodulation,[],[f823,f437])).
% 0.21/0.48  fof(f437,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | ~spl5_66),
% 0.21/0.48    inference(avatar_component_clause,[],[f436])).
% 0.21/0.48  fof(f436,plain,(
% 0.21/0.48    spl5_66 <=> k1_xboole_0 = sK1),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_66])])).
% 0.21/0.48  fof(f823,plain,(
% 0.21/0.48    ~v1_funct_2(k2_funct_1(sK2),sK1,k1_xboole_0) | (spl5_14 | ~spl5_55)),
% 0.21/0.48    inference(forward_demodulation,[],[f135,f355])).
% 0.21/0.48  fof(f355,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | ~spl5_55),
% 0.21/0.48    inference(avatar_component_clause,[],[f354])).
% 0.21/0.48  fof(f354,plain,(
% 0.21/0.48    spl5_55 <=> k1_xboole_0 = sK0),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_55])])).
% 0.21/0.48  fof(f135,plain,(
% 0.21/0.48    ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | spl5_14),
% 0.21/0.48    inference(avatar_component_clause,[],[f134])).
% 0.21/0.48  fof(f134,plain,(
% 0.21/0.48    spl5_14 <=> v1_funct_2(k2_funct_1(sK2),sK1,sK0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_14])])).
% 0.21/0.48  fof(f798,plain,(
% 0.21/0.48    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_xboole_0) | (~spl5_94 | ~spl5_98)),
% 0.21/0.48    inference(backward_demodulation,[],[f774,f795])).
% 0.21/0.48  fof(f795,plain,(
% 0.21/0.48    k1_xboole_0 = k1_relat_1(sK2) | ~spl5_98),
% 0.21/0.48    inference(avatar_component_clause,[],[f794])).
% 0.21/0.48  fof(f794,plain,(
% 0.21/0.48    spl5_98 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_98])])).
% 0.21/0.48  fof(f774,plain,(
% 0.21/0.48    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_relat_1(sK2)) | ~spl5_94),
% 0.21/0.48    inference(avatar_component_clause,[],[f773])).
% 0.21/0.48  fof(f773,plain,(
% 0.21/0.48    spl5_94 <=> v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_relat_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_94])])).
% 0.21/0.48  fof(f815,plain,(
% 0.21/0.48    ~spl5_61 | ~spl5_15 | spl5_13 | ~spl5_36 | ~spl5_37 | ~spl5_44 | ~spl5_47 | ~spl5_52 | ~spl5_70),
% 0.21/0.48    inference(avatar_split_clause,[],[f598,f528,f333,f299,f283,f241,f237,f131,f137,f395])).
% 0.21/0.48  fof(f395,plain,(
% 0.21/0.48    spl5_61 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_61])])).
% 0.21/0.48  fof(f137,plain,(
% 0.21/0.48    spl5_15 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_15])])).
% 0.21/0.48  fof(f131,plain,(
% 0.21/0.48    spl5_13 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_13])])).
% 0.21/0.48  fof(f237,plain,(
% 0.21/0.48    spl5_36 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_36])])).
% 0.21/0.48  fof(f241,plain,(
% 0.21/0.48    spl5_37 <=> ! [X0] : k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_37])])).
% 0.21/0.48  fof(f283,plain,(
% 0.21/0.48    spl5_44 <=> sK1 = k2_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_44])])).
% 0.21/0.48  fof(f299,plain,(
% 0.21/0.48    spl5_47 <=> sK1 = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_47])])).
% 0.21/0.48  fof(f333,plain,(
% 0.21/0.48    spl5_52 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_52])])).
% 0.21/0.48  fof(f528,plain,(
% 0.21/0.48    spl5_70 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_70])])).
% 0.21/0.48  fof(f598,plain,(
% 0.21/0.48    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (spl5_13 | ~spl5_36 | ~spl5_37 | ~spl5_44 | ~spl5_47 | ~spl5_52 | ~spl5_70)),
% 0.21/0.48    inference(subsumption_resolution,[],[f597,f595])).
% 0.21/0.48  fof(f595,plain,(
% 0.21/0.48    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | (spl5_13 | ~spl5_37 | ~spl5_44 | ~spl5_70)),
% 0.21/0.48    inference(forward_demodulation,[],[f581,f242])).
% 0.21/0.48  fof(f242,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) ) | ~spl5_37),
% 0.21/0.48    inference(avatar_component_clause,[],[f241])).
% 0.21/0.48  fof(f581,plain,(
% 0.21/0.48    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK0))) | (spl5_13 | ~spl5_44 | ~spl5_70)),
% 0.21/0.48    inference(backward_demodulation,[],[f132,f577])).
% 0.21/0.48  fof(f577,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | (~spl5_44 | ~spl5_70)),
% 0.21/0.48    inference(backward_demodulation,[],[f284,f529])).
% 0.21/0.48  fof(f529,plain,(
% 0.21/0.48    k1_xboole_0 = k2_relat_1(sK2) | ~spl5_70),
% 0.21/0.48    inference(avatar_component_clause,[],[f528])).
% 0.21/0.48  fof(f284,plain,(
% 0.21/0.48    sK1 = k2_relat_1(sK2) | ~spl5_44),
% 0.21/0.48    inference(avatar_component_clause,[],[f283])).
% 0.21/0.48  fof(f132,plain,(
% 0.21/0.48    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | spl5_13),
% 0.21/0.48    inference(avatar_component_clause,[],[f131])).
% 0.21/0.48  fof(f597,plain,(
% 0.21/0.48    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_36 | ~spl5_37 | ~spl5_44 | ~spl5_47 | ~spl5_52 | ~spl5_70)),
% 0.21/0.48    inference(forward_demodulation,[],[f588,f242])).
% 0.21/0.48  fof(f588,plain,(
% 0.21/0.48    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k1_relat_1(sK2)))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_36 | ~spl5_44 | ~spl5_47 | ~spl5_52 | ~spl5_70)),
% 0.21/0.48    inference(backward_demodulation,[],[f499,f577])).
% 0.21/0.48  fof(f499,plain,(
% 0.21/0.48    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k1_relat_1(sK2)))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_36 | ~spl5_47 | ~spl5_52)),
% 0.21/0.48    inference(backward_demodulation,[],[f492,f334])).
% 0.21/0.48  fof(f334,plain,(
% 0.21/0.48    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl5_52),
% 0.21/0.48    inference(avatar_component_clause,[],[f333])).
% 0.21/0.48  fof(f492,plain,(
% 0.21/0.48    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,k2_relat_1(k2_funct_1(sK2))))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_36 | ~spl5_47)),
% 0.21/0.48    inference(superposition,[],[f238,f300])).
% 0.21/0.48  fof(f300,plain,(
% 0.21/0.48    sK1 = k1_relat_1(k2_funct_1(sK2)) | ~spl5_47),
% 0.21/0.48    inference(avatar_component_clause,[],[f299])).
% 0.21/0.48  fof(f238,plain,(
% 0.21/0.48    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl5_36),
% 0.21/0.48    inference(avatar_component_clause,[],[f237])).
% 0.21/0.48  fof(f814,plain,(
% 0.21/0.48    spl5_72 | spl5_98 | ~spl5_44 | ~spl5_45 | ~spl5_53 | ~spl5_70 | ~spl5_93),
% 0.21/0.48    inference(avatar_split_clause,[],[f771,f767,f528,f347,f287,f283,f794,f568])).
% 0.21/0.48  fof(f287,plain,(
% 0.21/0.48    spl5_45 <=> ! [X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_45])])).
% 0.21/0.48  fof(f347,plain,(
% 0.21/0.48    spl5_53 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_53])])).
% 0.21/0.48  fof(f767,plain,(
% 0.21/0.48    spl5_93 <=> v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_93])])).
% 0.21/0.48  fof(f771,plain,(
% 0.21/0.48    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2 | (~spl5_44 | ~spl5_45 | ~spl5_53 | ~spl5_70 | ~spl5_93)),
% 0.21/0.48    inference(subsumption_resolution,[],[f770,f585])).
% 0.21/0.48  fof(f585,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) | (~spl5_44 | ~spl5_53 | ~spl5_70)),
% 0.21/0.48    inference(backward_demodulation,[],[f348,f577])).
% 0.21/0.48  fof(f348,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~spl5_53),
% 0.21/0.48    inference(avatar_component_clause,[],[f347])).
% 0.21/0.48  fof(f770,plain,(
% 0.21/0.48    k1_xboole_0 = k1_relat_1(sK2) | k1_xboole_0 = sK2 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k1_xboole_0))) | (~spl5_45 | ~spl5_93)),
% 0.21/0.48    inference(resolution,[],[f768,f288])).
% 0.21/0.48  fof(f288,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))) ) | ~spl5_45),
% 0.21/0.48    inference(avatar_component_clause,[],[f287])).
% 0.21/0.48  fof(f768,plain,(
% 0.21/0.48    v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | ~spl5_93),
% 0.21/0.48    inference(avatar_component_clause,[],[f767])).
% 0.21/0.48  fof(f796,plain,(
% 0.21/0.48    spl5_97 | spl5_98 | ~spl5_60 | ~spl5_63),
% 0.21/0.48    inference(avatar_split_clause,[],[f724,f412,f387,f794,f791])).
% 0.21/0.48  fof(f387,plain,(
% 0.21/0.48    spl5_60 <=> m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_60])])).
% 0.21/0.48  fof(f412,plain,(
% 0.21/0.48    spl5_63 <=> ! [X3,X2] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(X3) | ~v1_funct_2(X3,k1_xboole_0,X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_63])])).
% 0.21/0.48  fof(f724,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k1_relat_1(sK2) | ~v1_funct_2(sK2,k1_xboole_0,X0)) ) | (~spl5_60 | ~spl5_63)),
% 0.21/0.48    inference(resolution,[],[f388,f413])).
% 0.21/0.48  fof(f413,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(X3) | ~v1_funct_2(X3,k1_xboole_0,X2)) ) | ~spl5_63),
% 0.21/0.48    inference(avatar_component_clause,[],[f412])).
% 0.21/0.48  fof(f388,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | ~spl5_60),
% 0.21/0.48    inference(avatar_component_clause,[],[f387])).
% 0.21/0.48  fof(f775,plain,(
% 0.21/0.48    spl5_94 | ~spl5_44 | ~spl5_62 | ~spl5_70),
% 0.21/0.48    inference(avatar_split_clause,[],[f587,f528,f398,f283,f773])).
% 0.21/0.48  fof(f398,plain,(
% 0.21/0.48    spl5_62 <=> v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_62])])).
% 0.21/0.48  fof(f587,plain,(
% 0.21/0.48    v1_funct_2(k2_funct_1(sK2),k1_xboole_0,k1_relat_1(sK2)) | (~spl5_44 | ~spl5_62 | ~spl5_70)),
% 0.21/0.48    inference(backward_demodulation,[],[f399,f577])).
% 0.21/0.48  fof(f399,plain,(
% 0.21/0.48    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~spl5_62),
% 0.21/0.48    inference(avatar_component_clause,[],[f398])).
% 0.21/0.48  fof(f769,plain,(
% 0.21/0.48    spl5_93 | ~spl5_44 | ~spl5_49 | ~spl5_70),
% 0.21/0.48    inference(avatar_split_clause,[],[f584,f528,f318,f283,f767])).
% 0.21/0.48  fof(f318,plain,(
% 0.21/0.48    spl5_49 <=> v1_funct_2(sK2,k1_relat_1(sK2),sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_49])])).
% 0.21/0.48  fof(f584,plain,(
% 0.21/0.48    v1_funct_2(sK2,k1_relat_1(sK2),k1_xboole_0) | (~spl5_44 | ~spl5_49 | ~spl5_70)),
% 0.21/0.48    inference(backward_demodulation,[],[f319,f577])).
% 0.21/0.48  fof(f319,plain,(
% 0.21/0.48    v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~spl5_49),
% 0.21/0.48    inference(avatar_component_clause,[],[f318])).
% 0.21/0.48  fof(f729,plain,(
% 0.21/0.48    spl5_87 | ~spl5_55 | ~spl5_74),
% 0.21/0.48    inference(avatar_split_clause,[],[f712,f626,f354,f727])).
% 0.21/0.48  fof(f626,plain,(
% 0.21/0.48    spl5_74 <=> v1_funct_2(k1_xboole_0,sK0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_74])])).
% 0.21/0.48  fof(f712,plain,(
% 0.21/0.48    v1_funct_2(k1_xboole_0,k1_xboole_0,k1_xboole_0) | (~spl5_55 | ~spl5_74)),
% 0.21/0.48    inference(backward_demodulation,[],[f627,f355])).
% 0.21/0.48  fof(f627,plain,(
% 0.21/0.48    v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | ~spl5_74),
% 0.21/0.48    inference(avatar_component_clause,[],[f626])).
% 0.21/0.48  fof(f628,plain,(
% 0.21/0.48    spl5_74 | ~spl5_67 | ~spl5_72),
% 0.21/0.48    inference(avatar_split_clause,[],[f602,f568,f466,f626])).
% 0.21/0.48  fof(f466,plain,(
% 0.21/0.48    spl5_67 <=> v1_funct_2(sK2,sK0,k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_67])])).
% 0.21/0.48  fof(f602,plain,(
% 0.21/0.48    v1_funct_2(k1_xboole_0,sK0,k1_xboole_0) | (~spl5_67 | ~spl5_72)),
% 0.21/0.48    inference(backward_demodulation,[],[f467,f569])).
% 0.21/0.48  fof(f467,plain,(
% 0.21/0.48    v1_funct_2(sK2,sK0,k1_xboole_0) | ~spl5_67),
% 0.21/0.48    inference(avatar_component_clause,[],[f466])).
% 0.21/0.48  fof(f573,plain,(
% 0.21/0.48    ~spl5_61 | ~spl5_15 | spl5_13 | ~spl5_36 | ~spl5_47 | ~spl5_52 | ~spl5_68),
% 0.21/0.48    inference(avatar_split_clause,[],[f539,f495,f333,f299,f237,f131,f137,f395])).
% 0.21/0.48  fof(f495,plain,(
% 0.21/0.48    spl5_68 <=> sK0 = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_68])])).
% 0.21/0.48  fof(f539,plain,(
% 0.21/0.48    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (spl5_13 | ~spl5_36 | ~spl5_47 | ~spl5_52 | ~spl5_68)),
% 0.21/0.48    inference(subsumption_resolution,[],[f537,f132])).
% 0.21/0.48  fof(f537,plain,(
% 0.21/0.48    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_36 | ~spl5_47 | ~spl5_52 | ~spl5_68)),
% 0.21/0.48    inference(backward_demodulation,[],[f499,f531])).
% 0.21/0.48  fof(f531,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK2) | (~spl5_52 | ~spl5_68)),
% 0.21/0.48    inference(backward_demodulation,[],[f334,f496])).
% 0.21/0.48  fof(f496,plain,(
% 0.21/0.48    sK0 = k2_relat_1(k2_funct_1(sK2)) | ~spl5_68),
% 0.21/0.48    inference(avatar_component_clause,[],[f495])).
% 0.21/0.48  fof(f572,plain,(
% 0.21/0.48    spl5_65 | spl5_66 | ~spl5_3 | ~spl5_4 | ~spl5_64),
% 0.21/0.48    inference(avatar_split_clause,[],[f498,f420,f95,f91,f436,f433])).
% 0.21/0.48  fof(f433,plain,(
% 0.21/0.48    spl5_65 <=> sK0 = k1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_65])])).
% 0.21/0.48  fof(f91,plain,(
% 0.21/0.48    spl5_3 <=> v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_3])])).
% 0.21/0.48  fof(f95,plain,(
% 0.21/0.48    spl5_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_4])])).
% 0.21/0.48  fof(f420,plain,(
% 0.21/0.48    spl5_64 <=> ! [X3,X5,X4] : (k1_relat_1(X5) = X3 | k1_xboole_0 = X4 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_64])])).
% 0.21/0.48  fof(f498,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | sK0 = k1_relat_1(sK2) | (~spl5_3 | ~spl5_4 | ~spl5_64)),
% 0.21/0.48    inference(subsumption_resolution,[],[f482,f92])).
% 0.21/0.48  fof(f92,plain,(
% 0.21/0.48    v1_funct_2(sK2,sK0,sK1) | ~spl5_3),
% 0.21/0.48    inference(avatar_component_clause,[],[f91])).
% 0.21/0.48  fof(f482,plain,(
% 0.21/0.48    k1_xboole_0 = sK1 | sK0 = k1_relat_1(sK2) | ~v1_funct_2(sK2,sK0,sK1) | (~spl5_4 | ~spl5_64)),
% 0.21/0.48    inference(resolution,[],[f96,f421])).
% 0.21/0.48  fof(f421,plain,(
% 0.21/0.48    ( ! [X4,X5,X3] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | k1_xboole_0 = X4 | k1_relat_1(X5) = X3 | ~v1_funct_2(X5,X3,X4)) ) | ~spl5_64),
% 0.21/0.48    inference(avatar_component_clause,[],[f420])).
% 0.21/0.48  fof(f96,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | ~spl5_4),
% 0.21/0.48    inference(avatar_component_clause,[],[f95])).
% 0.21/0.48  fof(f530,plain,(
% 0.21/0.48    spl5_70 | ~spl5_44 | ~spl5_66),
% 0.21/0.48    inference(avatar_split_clause,[],[f506,f436,f283,f528])).
% 0.21/0.48  fof(f506,plain,(
% 0.21/0.48    k1_xboole_0 = k2_relat_1(sK2) | (~spl5_44 | ~spl5_66)),
% 0.21/0.48    inference(backward_demodulation,[],[f284,f437])).
% 0.21/0.48  fof(f497,plain,(
% 0.21/0.48    spl5_68 | ~spl5_52 | ~spl5_65),
% 0.21/0.48    inference(avatar_split_clause,[],[f473,f433,f333,f495])).
% 0.21/0.48  fof(f473,plain,(
% 0.21/0.48    sK0 = k2_relat_1(k2_funct_1(sK2)) | (~spl5_52 | ~spl5_65)),
% 0.21/0.48    inference(backward_demodulation,[],[f334,f434])).
% 0.21/0.48  fof(f434,plain,(
% 0.21/0.48    sK0 = k1_relat_1(sK2) | ~spl5_65),
% 0.21/0.48    inference(avatar_component_clause,[],[f433])).
% 0.21/0.48  fof(f468,plain,(
% 0.21/0.48    spl5_67 | ~spl5_3 | ~spl5_66),
% 0.21/0.48    inference(avatar_split_clause,[],[f447,f436,f91,f466])).
% 0.21/0.48  fof(f447,plain,(
% 0.21/0.48    v1_funct_2(sK2,sK0,k1_xboole_0) | (~spl5_3 | ~spl5_66)),
% 0.21/0.48    inference(backward_demodulation,[],[f92,f437])).
% 0.21/0.48  fof(f445,plain,(
% 0.21/0.48    spl5_14 | ~spl5_62 | ~spl5_65),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f444])).
% 0.21/0.48  fof(f444,plain,(
% 0.21/0.48    $false | (spl5_14 | ~spl5_62 | ~spl5_65)),
% 0.21/0.48    inference(subsumption_resolution,[],[f439,f135])).
% 0.21/0.48  fof(f439,plain,(
% 0.21/0.48    v1_funct_2(k2_funct_1(sK2),sK1,sK0) | (~spl5_62 | ~spl5_65)),
% 0.21/0.48    inference(backward_demodulation,[],[f399,f434])).
% 0.21/0.48  fof(f422,plain,(
% 0.21/0.48    spl5_64 | ~spl5_40 | ~spl5_51),
% 0.21/0.48    inference(avatar_split_clause,[],[f341,f326,f255,f420])).
% 0.21/0.48  fof(f255,plain,(
% 0.21/0.48    spl5_40 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_40])])).
% 0.21/0.48  fof(f326,plain,(
% 0.21/0.48    spl5_51 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_51])])).
% 0.21/0.48  fof(f341,plain,(
% 0.21/0.48    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | k1_xboole_0 = X4 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4)) ) | (~spl5_40 | ~spl5_51)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f338])).
% 0.21/0.48  fof(f338,plain,(
% 0.21/0.48    ( ! [X4,X5,X3] : (k1_relat_1(X5) = X3 | k1_xboole_0 = X4 | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4))) | ~v1_funct_2(X5,X3,X4) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X3,X4)))) ) | (~spl5_40 | ~spl5_51)),
% 0.21/0.48    inference(superposition,[],[f327,f256])).
% 0.21/0.48  fof(f256,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_40),
% 0.21/0.48    inference(avatar_component_clause,[],[f255])).
% 0.21/0.48  fof(f327,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k1_relset_1(X0,X1,X2) = X0 | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1)) ) | ~spl5_51),
% 0.21/0.48    inference(avatar_component_clause,[],[f326])).
% 0.21/0.48  % (21250)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.21/0.48  fof(f418,plain,(
% 0.21/0.48    ~spl5_30 | ~spl5_1 | ~spl5_25 | spl5_61),
% 0.21/0.48    inference(avatar_split_clause,[],[f410,f395,f180,f83,f204])).
% 0.21/0.48  fof(f204,plain,(
% 0.21/0.48    spl5_30 <=> v1_relat_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_30])])).
% 0.21/0.48  fof(f83,plain,(
% 0.21/0.48    spl5_1 <=> v1_funct_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_1])])).
% 0.21/0.48  fof(f180,plain,(
% 0.21/0.48    spl5_25 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_25])])).
% 0.21/0.48  fof(f410,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | (~spl5_1 | ~spl5_25 | spl5_61)),
% 0.21/0.48    inference(subsumption_resolution,[],[f408,f84])).
% 0.21/0.48  fof(f84,plain,(
% 0.21/0.48    v1_funct_1(sK2) | ~spl5_1),
% 0.21/0.48    inference(avatar_component_clause,[],[f83])).
% 0.21/0.48  fof(f408,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl5_25 | spl5_61)),
% 0.21/0.48    inference(resolution,[],[f396,f181])).
% 0.21/0.48  fof(f181,plain,(
% 0.21/0.48    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl5_25),
% 0.21/0.48    inference(avatar_component_clause,[],[f180])).
% 0.21/0.48  fof(f396,plain,(
% 0.21/0.48    ~v1_relat_1(k2_funct_1(sK2)) | spl5_61),
% 0.21/0.48    inference(avatar_component_clause,[],[f395])).
% 0.21/0.48  fof(f414,plain,(
% 0.21/0.48    spl5_63 | ~spl5_37 | ~spl5_40 | ~spl5_48),
% 0.21/0.48    inference(avatar_split_clause,[],[f309,f303,f255,f241,f412])).
% 0.21/0.48  fof(f303,plain,(
% 0.21/0.48    spl5_48 <=> ! [X1,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_48])])).
% 0.21/0.48  fof(f309,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(X3) | ~v1_funct_2(X3,k1_xboole_0,X2)) ) | (~spl5_37 | ~spl5_40 | ~spl5_48)),
% 0.21/0.48    inference(duplicate_literal_removal,[],[f308])).
% 0.21/0.48  fof(f308,plain,(
% 0.21/0.48    ( ! [X2,X3] : (~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relat_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X3,k1_xboole_0,X2)) ) | (~spl5_37 | ~spl5_40 | ~spl5_48)),
% 0.21/0.48    inference(forward_demodulation,[],[f306,f242])).
% 0.21/0.48  fof(f306,plain,(
% 0.21/0.48    ( ! [X2,X3] : (k1_xboole_0 = k1_relat_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X3,k1_xboole_0,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X2)))) ) | (~spl5_40 | ~spl5_48)),
% 0.21/0.48    inference(superposition,[],[f304,f256])).
% 0.21/0.48  % (21247)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.48  fof(f304,plain,(
% 0.21/0.48    ( ! [X2,X1] : (k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | ~v1_funct_2(X2,k1_xboole_0,X1)) ) | ~spl5_48),
% 0.21/0.48    inference(avatar_component_clause,[],[f303])).
% 0.21/0.48  fof(f400,plain,(
% 0.21/0.48    ~spl5_61 | ~spl5_15 | spl5_62 | ~spl5_4 | ~spl5_5 | ~spl5_32 | ~spl5_42 | ~spl5_43 | ~spl5_52),
% 0.21/0.48    inference(avatar_split_clause,[],[f337,f333,f269,f263,f215,f99,f95,f398,f137,f395])).
% 0.21/0.48  fof(f99,plain,(
% 0.21/0.48    spl5_5 <=> sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_5])])).
% 0.21/0.48  fof(f215,plain,(
% 0.21/0.48    spl5_32 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_32])])).
% 0.21/0.48  fof(f263,plain,(
% 0.21/0.48    spl5_42 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_42])])).
% 0.21/0.48  fof(f269,plain,(
% 0.21/0.48    spl5_43 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_43])])).
% 0.21/0.48  fof(f337,plain,(
% 0.21/0.48    v1_funct_2(k2_funct_1(sK2),sK1,k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_4 | ~spl5_5 | ~spl5_32 | ~spl5_42 | ~spl5_43 | ~spl5_52)),
% 0.21/0.48    inference(backward_demodulation,[],[f279,f334])).
% 0.21/0.48  fof(f279,plain,(
% 0.21/0.48    v1_funct_2(k2_funct_1(sK2),sK1,k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_4 | ~spl5_5 | ~spl5_32 | ~spl5_42 | ~spl5_43)),
% 0.21/0.48    inference(backward_demodulation,[],[f275,f278])).
% 0.21/0.48  fof(f278,plain,(
% 0.21/0.48    sK1 = k2_relat_1(sK2) | (~spl5_4 | ~spl5_5 | ~spl5_42)),
% 0.21/0.48    inference(subsumption_resolution,[],[f276,f96])).
% 0.21/0.48  fof(f276,plain,(
% 0.21/0.48    sK1 = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1))) | (~spl5_5 | ~spl5_42)),
% 0.21/0.48    inference(superposition,[],[f264,f100])).
% 0.21/0.48  fof(f100,plain,(
% 0.21/0.48    sK1 = k2_relset_1(sK0,sK1,sK2) | ~spl5_5),
% 0.21/0.48    inference(avatar_component_clause,[],[f99])).
% 0.21/0.48  fof(f264,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_42),
% 0.21/0.48    inference(avatar_component_clause,[],[f263])).
% 0.21/0.48  fof(f275,plain,(
% 0.21/0.48    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl5_32 | ~spl5_43)),
% 0.21/0.48    inference(superposition,[],[f216,f270])).
% 0.21/0.48  fof(f270,plain,(
% 0.21/0.48    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl5_43),
% 0.21/0.48    inference(avatar_component_clause,[],[f269])).
% 0.21/0.48  fof(f216,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl5_32),
% 0.21/0.48    inference(avatar_component_clause,[],[f215])).
% 0.21/0.48  fof(f389,plain,(
% 0.21/0.48    spl5_60 | ~spl5_4 | ~spl5_37 | ~spl5_55),
% 0.21/0.48    inference(avatar_split_clause,[],[f376,f354,f241,f95,f387])).
% 0.21/0.48  fof(f376,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k1_xboole_0)) | (~spl5_4 | ~spl5_37 | ~spl5_55)),
% 0.21/0.48    inference(forward_demodulation,[],[f373,f242])).
% 0.21/0.48  fof(f373,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,sK1))) | (~spl5_4 | ~spl5_55)),
% 0.21/0.48    inference(backward_demodulation,[],[f96,f355])).
% 0.21/0.48  fof(f371,plain,(
% 0.21/0.48    ~spl5_13 | ~spl5_40 | ~spl5_47 | spl5_54),
% 0.21/0.48    inference(avatar_split_clause,[],[f360,f351,f299,f255,f131])).
% 0.21/0.48  fof(f351,plain,(
% 0.21/0.48    spl5_54 <=> sK1 = k1_relset_1(sK1,sK0,k2_funct_1(sK2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_54])])).
% 0.21/0.48  fof(f360,plain,(
% 0.21/0.48    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl5_40 | ~spl5_47 | spl5_54)),
% 0.21/0.48    inference(subsumption_resolution,[],[f358,f300])).
% 0.21/0.48  fof(f358,plain,(
% 0.21/0.48    sK1 != k1_relat_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (~spl5_40 | spl5_54)),
% 0.21/0.48    inference(superposition,[],[f352,f256])).
% 0.21/0.48  fof(f352,plain,(
% 0.21/0.48    sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | spl5_54),
% 0.21/0.48    inference(avatar_component_clause,[],[f351])).
% 0.21/0.48  fof(f356,plain,(
% 0.21/0.48    ~spl5_13 | ~spl5_54 | spl5_55 | spl5_14 | ~spl5_50),
% 0.21/0.48    inference(avatar_split_clause,[],[f329,f322,f134,f354,f351,f131])).
% 0.21/0.48  fof(f322,plain,(
% 0.21/0.48    spl5_50 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_50])])).
% 0.21/0.48  fof(f329,plain,(
% 0.21/0.48    k1_xboole_0 = sK0 | sK1 != k1_relset_1(sK1,sK0,k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0))) | (spl5_14 | ~spl5_50)),
% 0.21/0.48    inference(resolution,[],[f323,f135])).
% 0.21/0.48  fof(f323,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_50),
% 0.21/0.48    inference(avatar_component_clause,[],[f322])).
% 0.21/0.48  fof(f349,plain,(
% 0.21/0.48    ~spl5_30 | spl5_53 | ~spl5_1 | ~spl5_36 | ~spl5_44),
% 0.21/0.48    inference(avatar_split_clause,[],[f296,f283,f237,f83,f347,f204])).
% 0.21/0.48  fof(f296,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_relat_1(sK2) | (~spl5_1 | ~spl5_36 | ~spl5_44)),
% 0.21/0.48    inference(subsumption_resolution,[],[f294,f84])).
% 0.21/0.48  fof(f294,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),sK1))) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl5_36 | ~spl5_44)),
% 0.21/0.48    inference(superposition,[],[f238,f284])).
% 0.21/0.48  fof(f335,plain,(
% 0.21/0.48    spl5_52 | ~spl5_30 | ~spl5_1 | ~spl5_2 | ~spl5_39),
% 0.21/0.48    inference(avatar_split_clause,[],[f273,f249,f87,f83,f204,f333])).
% 0.21/0.48  fof(f87,plain,(
% 0.21/0.48    spl5_2 <=> v2_funct_1(sK2)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_2])])).
% 0.21/0.48  fof(f249,plain,(
% 0.21/0.48    spl5_39 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_39])])).
% 0.21/0.48  fof(f273,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl5_1 | ~spl5_2 | ~spl5_39)),
% 0.21/0.48    inference(subsumption_resolution,[],[f272,f84])).
% 0.21/0.48  fof(f272,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl5_2 | ~spl5_39)),
% 0.21/0.48    inference(resolution,[],[f250,f88])).
% 0.21/0.48  fof(f88,plain,(
% 0.21/0.48    v2_funct_1(sK2) | ~spl5_2),
% 0.21/0.48    inference(avatar_component_clause,[],[f87])).
% 0.21/0.48  fof(f250,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) ) | ~spl5_39),
% 0.21/0.48    inference(avatar_component_clause,[],[f249])).
% 0.21/0.48  fof(f328,plain,(
% 0.21/0.48    spl5_51),
% 0.21/0.48    inference(avatar_split_clause,[],[f73,f326])).
% 0.21/0.48  fof(f73,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f34,plain,(
% 0.21/0.48    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(flattening,[],[f33])).
% 0.21/0.48  fof(f33,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f15])).
% 0.21/0.48  fof(f15,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.48  fof(f324,plain,(
% 0.21/0.48    spl5_50),
% 0.21/0.48    inference(avatar_split_clause,[],[f72,f322])).
% 0.21/0.48  fof(f72,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) != X0 | v1_funct_2(X2,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f320,plain,(
% 0.21/0.48    ~spl5_30 | spl5_49 | ~spl5_1 | ~spl5_32 | ~spl5_44),
% 0.21/0.48    inference(avatar_split_clause,[],[f297,f283,f215,f83,f318,f204])).
% 0.21/0.48  fof(f297,plain,(
% 0.21/0.48    v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_relat_1(sK2) | (~spl5_1 | ~spl5_32 | ~spl5_44)),
% 0.21/0.48    inference(subsumption_resolution,[],[f295,f84])).
% 0.21/0.48  fof(f295,plain,(
% 0.21/0.48    v1_funct_2(sK2,k1_relat_1(sK2),sK1) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl5_32 | ~spl5_44)),
% 0.21/0.48    inference(superposition,[],[f216,f284])).
% 0.21/0.48  fof(f305,plain,(
% 0.21/0.48    spl5_48 | ~spl5_6 | ~spl5_34),
% 0.21/0.48    inference(avatar_split_clause,[],[f230,f223,f103,f303])).
% 0.21/0.48  fof(f103,plain,(
% 0.21/0.48    spl5_6 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_6])])).
% 0.21/0.48  fof(f223,plain,(
% 0.21/0.48    spl5_34 <=> ! [X1,X0] : (~v1_xboole_0(X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_34])])).
% 0.21/0.48  fof(f230,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k1_xboole_0)) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) ) | (~spl5_6 | ~spl5_34)),
% 0.21/0.48    inference(backward_demodulation,[],[f76,f227])).
% 0.21/0.48  fof(f227,plain,(
% 0.21/0.48    ( ! [X0] : (k1_xboole_0 = k2_zfmisc_1(k1_xboole_0,X0)) ) | (~spl5_6 | ~spl5_34)),
% 0.21/0.48    inference(resolution,[],[f224,f104])).
% 0.21/0.48  fof(f104,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0) | ~spl5_6),
% 0.21/0.48    inference(avatar_component_clause,[],[f103])).
% 0.21/0.48  fof(f224,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) ) | ~spl5_34),
% 0.21/0.48    inference(avatar_component_clause,[],[f223])).
% 0.21/0.48  fof(f76,plain,(
% 0.21/0.48    ( ! [X2,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,X1))) | k1_xboole_0 = k1_relset_1(k1_xboole_0,X1,X2) | ~v1_funct_2(X2,k1_xboole_0,X1)) )),
% 0.21/0.48    inference(equality_resolution,[],[f71])).
% 0.21/0.48  fof(f71,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X0 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f301,plain,(
% 0.21/0.48    spl5_47 | ~spl5_4 | ~spl5_5 | ~spl5_42 | ~spl5_43),
% 0.21/0.48    inference(avatar_split_clause,[],[f281,f269,f263,f99,f95,f299])).
% 0.21/0.48  fof(f281,plain,(
% 0.21/0.48    sK1 = k1_relat_1(k2_funct_1(sK2)) | (~spl5_4 | ~spl5_5 | ~spl5_42 | ~spl5_43)),
% 0.21/0.48    inference(backward_demodulation,[],[f270,f278])).
% 0.21/0.48  fof(f289,plain,(
% 0.21/0.48    spl5_45),
% 0.21/0.48    inference(avatar_split_clause,[],[f78,f287])).
% 0.21/0.48  fof(f78,plain,(
% 0.21/0.48    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 0.21/0.48    inference(equality_resolution,[],[f69])).
% 0.21/0.48  fof(f69,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f34])).
% 0.21/0.48  fof(f285,plain,(
% 0.21/0.48    spl5_44 | ~spl5_4 | ~spl5_5 | ~spl5_42),
% 0.21/0.48    inference(avatar_split_clause,[],[f278,f263,f99,f95,f283])).
% 0.21/0.48  fof(f271,plain,(
% 0.21/0.48    spl5_43 | ~spl5_30 | ~spl5_1 | ~spl5_2 | ~spl5_38),
% 0.21/0.48    inference(avatar_split_clause,[],[f267,f245,f87,f83,f204,f269])).
% 0.21/0.48  fof(f245,plain,(
% 0.21/0.48    spl5_38 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_38])])).
% 0.21/0.48  fof(f267,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl5_1 | ~spl5_2 | ~spl5_38)),
% 0.21/0.48    inference(subsumption_resolution,[],[f266,f84])).
% 0.21/0.48  fof(f266,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | (~spl5_2 | ~spl5_38)),
% 0.21/0.48    inference(resolution,[],[f246,f88])).
% 0.21/0.48  fof(f246,plain,(
% 0.21/0.48    ( ! [X0] : (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) ) | ~spl5_38),
% 0.21/0.48    inference(avatar_component_clause,[],[f245])).
% 0.21/0.48  fof(f265,plain,(
% 0.21/0.48    spl5_42),
% 0.21/0.48    inference(avatar_split_clause,[],[f67,f263])).
% 0.21/0.48  fof(f67,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f32])).
% 0.21/0.48  fof(f32,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f14])).
% 0.21/0.48  fof(f14,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.48  fof(f257,plain,(
% 0.21/0.48    spl5_40),
% 0.21/0.48    inference(avatar_split_clause,[],[f66,f255])).
% 0.21/0.48  fof(f66,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f31])).
% 0.21/0.48  fof(f31,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f13])).
% 0.21/0.48  fof(f13,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.48  fof(f251,plain,(
% 0.21/0.48    spl5_39),
% 0.21/0.48    inference(avatar_split_clause,[],[f55,f249])).
% 0.21/0.48  fof(f55,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f28,plain,(
% 0.21/0.48    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f27])).
% 0.21/0.48  fof(f27,plain,(
% 0.21/0.48    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f11])).
% 0.21/0.48  fof(f11,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.48  fof(f247,plain,(
% 0.21/0.48    spl5_38),
% 0.21/0.48    inference(avatar_split_clause,[],[f54,f245])).
% 0.21/0.48  fof(f54,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f28])).
% 0.21/0.48  fof(f243,plain,(
% 0.21/0.48    spl5_37 | ~spl5_6 | ~spl5_34),
% 0.21/0.48    inference(avatar_split_clause,[],[f227,f223,f103,f241])).
% 0.21/0.48  fof(f239,plain,(
% 0.21/0.48    spl5_36),
% 0.21/0.48    inference(avatar_split_clause,[],[f51,f237])).
% 0.21/0.48  fof(f51,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f24,plain,(
% 0.21/0.48    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f23])).
% 0.21/0.48  fof(f23,plain,(
% 0.21/0.48    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f17])).
% 0.21/0.48  fof(f17,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_funct_2)).
% 0.21/0.48  fof(f225,plain,(
% 0.21/0.48    spl5_34 | ~spl5_16 | ~spl5_22),
% 0.21/0.48    inference(avatar_split_clause,[],[f192,f167,f141,f223])).
% 0.21/0.48  fof(f141,plain,(
% 0.21/0.48    spl5_16 <=> ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0)),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_16])])).
% 0.21/0.48  fof(f167,plain,(
% 0.21/0.48    spl5_22 <=> ! [X1,X0] : (~v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_22])])).
% 0.21/0.48  fof(f192,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(X0) | k1_xboole_0 = k2_zfmisc_1(X0,X1)) ) | (~spl5_16 | ~spl5_22)),
% 0.21/0.48    inference(resolution,[],[f168,f142])).
% 0.21/0.48  fof(f142,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) ) | ~spl5_16),
% 0.21/0.48    inference(avatar_component_clause,[],[f141])).
% 0.21/0.48  fof(f168,plain,(
% 0.21/0.48    ( ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0)) ) | ~spl5_22),
% 0.21/0.48    inference(avatar_component_clause,[],[f167])).
% 0.21/0.48  fof(f217,plain,(
% 0.21/0.48    spl5_32),
% 0.21/0.48    inference(avatar_split_clause,[],[f50,f215])).
% 0.21/0.48  fof(f50,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f24])).
% 0.21/0.48  fof(f213,plain,(
% 0.21/0.48    ~spl5_4 | ~spl5_29 | spl5_30),
% 0.21/0.48    inference(avatar_contradiction_clause,[],[f211])).
% 0.21/0.48  fof(f211,plain,(
% 0.21/0.48    $false | (~spl5_4 | ~spl5_29 | spl5_30)),
% 0.21/0.48    inference(unit_resulting_resolution,[],[f205,f96,f199])).
% 0.21/0.48  fof(f199,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl5_29),
% 0.21/0.48    inference(avatar_component_clause,[],[f198])).
% 0.21/0.48  fof(f198,plain,(
% 0.21/0.48    spl5_29 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_29])])).
% 0.21/0.48  fof(f205,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | spl5_30),
% 0.21/0.48    inference(avatar_component_clause,[],[f204])).
% 0.21/0.48  fof(f206,plain,(
% 0.21/0.48    ~spl5_30 | ~spl5_1 | spl5_15 | ~spl5_26),
% 0.21/0.48    inference(avatar_split_clause,[],[f202,f184,f137,f83,f204])).
% 0.21/0.48  fof(f184,plain,(
% 0.21/0.48    spl5_26 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0)))),
% 0.21/0.48    introduced(avatar_definition,[new_symbols(naming,[spl5_26])])).
% 0.21/0.48  fof(f202,plain,(
% 0.21/0.48    ~v1_relat_1(sK2) | (~spl5_1 | spl5_15 | ~spl5_26)),
% 0.21/0.48    inference(subsumption_resolution,[],[f201,f84])).
% 0.21/0.48  fof(f201,plain,(
% 0.21/0.48    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl5_15 | ~spl5_26)),
% 0.21/0.48    inference(resolution,[],[f185,f138])).
% 0.21/0.48  fof(f138,plain,(
% 0.21/0.48    ~v1_funct_1(k2_funct_1(sK2)) | spl5_15),
% 0.21/0.48    inference(avatar_component_clause,[],[f137])).
% 0.21/0.48  fof(f185,plain,(
% 0.21/0.48    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl5_26),
% 0.21/0.48    inference(avatar_component_clause,[],[f184])).
% 0.21/0.48  fof(f200,plain,(
% 0.21/0.48    spl5_29),
% 0.21/0.48    inference(avatar_split_clause,[],[f65,f198])).
% 0.21/0.48  fof(f65,plain,(
% 0.21/0.48    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.48    inference(cnf_transformation,[],[f30])).
% 0.21/0.48  fof(f30,plain,(
% 0.21/0.48    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.48    inference(ennf_transformation,[],[f12])).
% 0.21/0.48  fof(f12,axiom,(
% 0.21/0.48    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.48  fof(f186,plain,(
% 0.21/0.48    spl5_26),
% 0.21/0.48    inference(avatar_split_clause,[],[f53,f184])).
% 0.21/0.48  fof(f53,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_funct_1(k2_funct_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f26,plain,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.48    inference(flattening,[],[f25])).
% 0.21/0.48  fof(f25,plain,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.48    inference(ennf_transformation,[],[f9])).
% 0.21/0.48  fof(f9,axiom,(
% 0.21/0.48    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.48  fof(f182,plain,(
% 0.21/0.48    spl5_25),
% 0.21/0.48    inference(avatar_split_clause,[],[f52,f180])).
% 0.21/0.48  fof(f52,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | v1_relat_1(k2_funct_1(X0))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f26])).
% 0.21/0.48  fof(f169,plain,(
% 0.21/0.48    spl5_22),
% 0.21/0.48    inference(avatar_split_clause,[],[f58,f167])).
% 0.21/0.48  fof(f58,plain,(
% 0.21/0.48    ( ! [X0,X1] : (~v1_xboole_0(X0) | v1_xboole_0(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.48    inference(cnf_transformation,[],[f29])).
% 0.21/0.48  fof(f29,plain,(
% 0.21/0.48    ! [X0,X1] : (v1_xboole_0(k2_zfmisc_1(X0,X1)) | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f4])).
% 0.21/0.48  fof(f4,axiom,(
% 0.21/0.48    ! [X0,X1] : (v1_xboole_0(X0) => v1_xboole_0(k2_zfmisc_1(X0,X1)))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc4_zfmisc_1)).
% 0.21/0.48  fof(f143,plain,(
% 0.21/0.48    spl5_16),
% 0.21/0.48    inference(avatar_split_clause,[],[f49,f141])).
% 0.21/0.48  fof(f49,plain,(
% 0.21/0.48    ( ! [X0] : (~v1_xboole_0(X0) | k1_xboole_0 = X0) )),
% 0.21/0.48    inference(cnf_transformation,[],[f22])).
% 0.21/0.48  fof(f22,plain,(
% 0.21/0.48    ! [X0] : (k1_xboole_0 = X0 | ~v1_xboole_0(X0))),
% 0.21/0.48    inference(ennf_transformation,[],[f3])).
% 0.21/0.48  fof(f3,axiom,(
% 0.21/0.48    ! [X0] : (v1_xboole_0(X0) => k1_xboole_0 = X0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).
% 0.21/0.48  fof(f139,plain,(
% 0.21/0.48    ~spl5_13 | ~spl5_14 | ~spl5_15),
% 0.21/0.48    inference(avatar_split_clause,[],[f38,f137,f134,f131])).
% 0.21/0.48  fof(f38,plain,(
% 0.21/0.48    ~v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),sK1,sK0) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(sK1,sK0)))),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f21,plain,(
% 0.21/0.48    ? [X0,X1,X2] : ((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2))),
% 0.21/0.48    inference(flattening,[],[f20])).
% 0.21/0.48  fof(f20,plain,(
% 0.21/0.48    ? [X0,X1,X2] : (((~m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(k2_funct_1(X2),X1,X0) | ~v1_funct_1(k2_funct_1(X2))) & (k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)))),
% 0.21/0.48    inference(ennf_transformation,[],[f19])).
% 0.21/0.48  fof(f19,negated_conjecture,(
% 0.21/0.48    ~! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.48    inference(negated_conjecture,[],[f18])).
% 0.21/0.48  fof(f18,conjecture,(
% 0.21/0.48    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.48  fof(f105,plain,(
% 0.21/0.48    spl5_6),
% 0.21/0.48    inference(avatar_split_clause,[],[f44,f103])).
% 0.21/0.48  fof(f44,plain,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    inference(cnf_transformation,[],[f2])).
% 0.21/0.48  fof(f2,axiom,(
% 0.21/0.48    v1_xboole_0(k1_xboole_0)),
% 0.21/0.48    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.48  fof(f101,plain,(
% 0.21/0.48    spl5_5),
% 0.21/0.48    inference(avatar_split_clause,[],[f43,f99])).
% 0.21/0.48  fof(f43,plain,(
% 0.21/0.48    sK1 = k2_relset_1(sK0,sK1,sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f97,plain,(
% 0.21/0.48    spl5_4),
% 0.21/0.48    inference(avatar_split_clause,[],[f41,f95])).
% 0.21/0.48  fof(f41,plain,(
% 0.21/0.48    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(sK0,sK1)))),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f93,plain,(
% 0.21/0.48    spl5_3),
% 0.21/0.48    inference(avatar_split_clause,[],[f40,f91])).
% 0.21/0.48  fof(f40,plain,(
% 0.21/0.48    v1_funct_2(sK2,sK0,sK1)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f89,plain,(
% 0.21/0.48    spl5_2),
% 0.21/0.48    inference(avatar_split_clause,[],[f42,f87])).
% 0.21/0.48  fof(f42,plain,(
% 0.21/0.48    v2_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  fof(f85,plain,(
% 0.21/0.48    spl5_1),
% 0.21/0.48    inference(avatar_split_clause,[],[f39,f83])).
% 0.21/0.48  fof(f39,plain,(
% 0.21/0.48    v1_funct_1(sK2)),
% 0.21/0.48    inference(cnf_transformation,[],[f21])).
% 0.21/0.48  % SZS output end Proof for theBenchmark
% 0.21/0.48  % (21251)------------------------------
% 0.21/0.48  % (21251)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.48  % (21251)Termination reason: Refutation
% 0.21/0.48  
% 0.21/0.48  % (21251)Memory used [KB]: 11001
% 0.21/0.48  % (21251)Time elapsed: 0.063 s
% 0.21/0.48  % (21251)------------------------------
% 0.21/0.48  % (21251)------------------------------
% 0.21/0.48  % (21248)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.49  % (21241)Success in time 0.121 s
%------------------------------------------------------------------------------
