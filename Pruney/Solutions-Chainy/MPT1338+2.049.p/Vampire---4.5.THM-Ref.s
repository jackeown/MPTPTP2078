%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:07 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  292 ( 731 expanded)
%              Number of leaves         :   65 ( 338 expanded)
%              Depth                    :   10
%              Number of atoms          : 1037 (2513 expanded)
%              Number of equality atoms :  189 ( 545 expanded)
%              Maximal formula depth    :   11 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f607,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f64,f68,f72,f76,f80,f84,f88,f92,f96,f100,f104,f108,f124,f128,f136,f147,f151,f155,f159,f163,f181,f188,f192,f196,f202,f210,f214,f226,f230,f242,f246,f256,f267,f279,f283,f292,f300,f311,f318,f322,f335,f339,f347,f351,f368,f378,f383,f390,f392,f445,f448,f472,f524,f552,f606])).

fof(f606,plain,
    ( ~ spl3_66
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_20
    | spl3_64
    | ~ spl3_77 ),
    inference(avatar_split_clause,[],[f584,f550,f402,f149,f66,f62,f443])).

fof(f443,plain,
    ( spl3_66
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f62,plain,
    ( spl3_1
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f66,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f149,plain,
    ( spl3_20
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f402,plain,
    ( spl3_64
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f550,plain,
    ( spl3_77
  <=> k1_xboole_0 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).

fof(f584,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_20
    | spl3_64
    | ~ spl3_77 ),
    inference(subsumption_resolution,[],[f583,f67])).

fof(f67,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f66])).

fof(f583,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_20
    | spl3_64
    | ~ spl3_77 ),
    inference(subsumption_resolution,[],[f582,f63])).

fof(f63,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f62])).

fof(f582,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_20
    | spl3_64
    | ~ spl3_77 ),
    inference(subsumption_resolution,[],[f578,f562])).

fof(f562,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k1_xboole_0)
    | spl3_64
    | ~ spl3_77 ),
    inference(backward_demodulation,[],[f547,f551])).

fof(f551,plain,
    ( k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl3_77 ),
    inference(avatar_component_clause,[],[f550])).

fof(f547,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | spl3_64 ),
    inference(avatar_component_clause,[],[f402])).

fof(f578,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k1_xboole_0)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_20
    | ~ spl3_77 ),
    inference(superposition,[],[f150,f551])).

fof(f150,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f149])).

fof(f552,plain,
    ( spl3_77
    | spl3_41
    | ~ spl3_1
    | ~ spl3_35
    | ~ spl3_40
    | ~ spl3_43
    | ~ spl3_44
    | ~ spl3_56
    | ~ spl3_63
    | ~ spl3_73 ),
    inference(avatar_split_clause,[],[f530,f522,f388,f345,f281,f277,f244,f224,f62,f251,f550])).

fof(f251,plain,
    ( spl3_41
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f224,plain,
    ( spl3_35
  <=> ! [X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X2
        | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f244,plain,
    ( spl3_40
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f277,plain,
    ( spl3_43
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f281,plain,
    ( spl3_44
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f345,plain,
    ( spl3_56
  <=> k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f388,plain,
    ( spl3_63
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).

fof(f522,plain,
    ( spl3_73
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).

fof(f530,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_35
    | ~ spl3_40
    | ~ spl3_43
    | ~ spl3_44
    | ~ spl3_56
    | ~ spl3_63
    | ~ spl3_73 ),
    inference(subsumption_resolution,[],[f525,f460])).

fof(f460,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_xboole_0)
    | ~ spl3_1
    | ~ spl3_40
    | ~ spl3_43
    | ~ spl3_44
    | ~ spl3_56
    | ~ spl3_63 ),
    inference(backward_demodulation,[],[f361,f389])).

fof(f389,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl3_63 ),
    inference(avatar_component_clause,[],[f388])).

fof(f361,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_1
    | ~ spl3_40
    | ~ spl3_43
    | ~ spl3_44
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f360,f63])).

fof(f360,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_40
    | ~ spl3_43
    | ~ spl3_44
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f359,f282])).

fof(f282,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f281])).

fof(f359,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ spl3_40
    | ~ spl3_43
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f357,f278])).

fof(f278,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f277])).

fof(f357,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ spl3_40
    | ~ spl3_56 ),
    inference(superposition,[],[f245,f346])).

fof(f346,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f345])).

fof(f245,plain,
    ( ! [X2,X0,X1] :
        ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f244])).

fof(f525,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_xboole_0)
    | ~ spl3_35
    | ~ spl3_73 ),
    inference(resolution,[],[f523,f225])).

fof(f225,plain,
    ( ! [X2,X0] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
        | k1_xboole_0 = X0
        | k1_xboole_0 = X2
        | ~ v1_funct_2(X2,X0,k1_xboole_0) )
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f224])).

fof(f523,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_xboole_0)))
    | ~ spl3_73 ),
    inference(avatar_component_clause,[],[f522])).

fof(f524,plain,
    ( spl3_73
    | ~ spl3_57
    | ~ spl3_63 ),
    inference(avatar_split_clause,[],[f459,f388,f349,f522])).

fof(f349,plain,
    ( spl3_57
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f459,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_xboole_0)))
    | ~ spl3_57
    | ~ spl3_63 ),
    inference(backward_demodulation,[],[f350,f389])).

fof(f350,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f349])).

fof(f472,plain,
    ( spl3_47
    | ~ spl3_56
    | ~ spl3_60
    | ~ spl3_63
    | ~ spl3_64 ),
    inference(avatar_contradiction_clause,[],[f471])).

fof(f471,plain,
    ( $false
    | spl3_47
    | ~ spl3_56
    | ~ spl3_60
    | ~ spl3_63
    | ~ spl3_64 ),
    inference(subsumption_resolution,[],[f470,f463])).

fof(f463,plain,
    ( k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_xboole_0,k2_funct_1(sK2))
    | ~ spl3_60
    | ~ spl3_63
    | ~ spl3_64 ),
    inference(backward_demodulation,[],[f431,f389])).

fof(f431,plain,
    ( k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_60
    | ~ spl3_64 ),
    inference(backward_demodulation,[],[f377,f403])).

fof(f403,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_64 ),
    inference(avatar_component_clause,[],[f402])).

fof(f377,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_60 ),
    inference(avatar_component_clause,[],[f376])).

fof(f376,plain,
    ( spl3_60
  <=> k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).

fof(f470,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_xboole_0,k2_funct_1(sK2))
    | spl3_47
    | ~ spl3_56
    | ~ spl3_63 ),
    inference(forward_demodulation,[],[f469,f458])).

fof(f458,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_xboole_0,k2_relat_1(sK2),sK2)
    | ~ spl3_56
    | ~ spl3_63 ),
    inference(backward_demodulation,[],[f346,f389])).

fof(f469,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_relat_1(sK2),sK2))
    | spl3_47
    | ~ spl3_63 ),
    inference(forward_demodulation,[],[f299,f389])).

fof(f299,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | spl3_47 ),
    inference(avatar_component_clause,[],[f298])).

fof(f298,plain,
    ( spl3_47
  <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f448,plain,
    ( ~ spl3_12
    | ~ spl3_44
    | spl3_66 ),
    inference(avatar_contradiction_clause,[],[f446])).

fof(f446,plain,
    ( $false
    | ~ spl3_12
    | ~ spl3_44
    | spl3_66 ),
    inference(unit_resulting_resolution,[],[f282,f444,f107])).

fof(f107,plain,
    ( ! [X2,X0,X1] :
        ( v1_relat_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f106])).

fof(f106,plain,
    ( spl3_12
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f444,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_66 ),
    inference(avatar_component_clause,[],[f443])).

fof(f445,plain,
    ( ~ spl3_66
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_21
    | spl3_61 ),
    inference(avatar_split_clause,[],[f400,f381,f153,f66,f62,f443])).

fof(f153,plain,
    ( spl3_21
  <=> ! [X0] :
        ( ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f381,plain,
    ( spl3_61
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f400,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_21
    | spl3_61 ),
    inference(subsumption_resolution,[],[f399,f67])).

fof(f399,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_1
    | ~ spl3_21
    | spl3_61 ),
    inference(subsumption_resolution,[],[f398,f63])).

fof(f398,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_21
    | spl3_61 ),
    inference(trivial_inequality_removal,[],[f397])).

fof(f397,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_21
    | spl3_61 ),
    inference(superposition,[],[f382,f154])).

fof(f154,plain,
    ( ! [X0] :
        ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        | ~ v1_funct_1(X0)
        | ~ v2_funct_1(X0)
        | ~ v1_relat_1(X0) )
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f153])).

fof(f382,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | spl3_61 ),
    inference(avatar_component_clause,[],[f381])).

fof(f392,plain,
    ( ~ spl3_1
    | ~ spl3_40
    | ~ spl3_43
    | ~ spl3_44
    | ~ spl3_56
    | spl3_62 ),
    inference(avatar_contradiction_clause,[],[f391])).

fof(f391,plain,
    ( $false
    | ~ spl3_1
    | ~ spl3_40
    | ~ spl3_43
    | ~ spl3_44
    | ~ spl3_56
    | spl3_62 ),
    inference(subsumption_resolution,[],[f386,f361])).

fof(f386,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | spl3_62 ),
    inference(avatar_component_clause,[],[f385])).

fof(f385,plain,
    ( spl3_62
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f390,plain,
    ( ~ spl3_62
    | spl3_63
    | ~ spl3_39
    | spl3_53
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f356,f349,f333,f240,f388,f385])).

fof(f240,plain,
    ( spl3_39
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f333,plain,
    ( spl3_53
  <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f356,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_39
    | spl3_53
    | ~ spl3_57 ),
    inference(subsumption_resolution,[],[f353,f334])).

fof(f334,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | spl3_53 ),
    inference(avatar_component_clause,[],[f333])).

fof(f353,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_39
    | ~ spl3_57 ),
    inference(resolution,[],[f350,f241])).

fof(f241,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_xboole_0 = X1
        | k1_relset_1(X0,X1,X2) = X0
        | ~ v1_funct_2(X2,X0,X1) )
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f240])).

fof(f383,plain,
    ( ~ spl3_61
    | spl3_54
    | ~ spl3_58 ),
    inference(avatar_split_clause,[],[f373,f366,f337,f381])).

fof(f337,plain,
    ( spl3_54
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f366,plain,
    ( spl3_58
  <=> k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f373,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | spl3_54
    | ~ spl3_58 ),
    inference(superposition,[],[f338,f367])).

fof(f367,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_58 ),
    inference(avatar_component_clause,[],[f366])).

fof(f338,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | spl3_54 ),
    inference(avatar_component_clause,[],[f337])).

fof(f378,plain,
    ( spl3_60
    | ~ spl3_22
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f355,f349,f157,f376])).

fof(f157,plain,
    ( spl3_22
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f355,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_22
    | ~ spl3_57 ),
    inference(resolution,[],[f350,f158])).

fof(f158,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) )
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f157])).

fof(f368,plain,
    ( spl3_58
    | ~ spl3_23
    | ~ spl3_57 ),
    inference(avatar_split_clause,[],[f354,f349,f161,f366])).

fof(f161,plain,
    ( spl3_23
  <=> ! [X1,X0,X2] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f354,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_23
    | ~ spl3_57 ),
    inference(resolution,[],[f350,f162])).

fof(f162,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) )
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f161])).

fof(f351,plain,
    ( spl3_57
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_43
    | ~ spl3_44
    | ~ spl3_50
    | ~ spl3_51
    | ~ spl3_52 ),
    inference(avatar_split_clause,[],[f329,f320,f316,f309,f281,f277,f66,f62,f349])).

fof(f309,plain,
    ( spl3_50
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f316,plain,
    ( spl3_51
  <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f320,plain,
    ( spl3_52
  <=> ! [X1,X0,X2] :
        ( ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,X2) != X1
        | ~ v2_funct_1(X2)
        | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f329,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_43
    | ~ spl3_44
    | ~ spl3_50
    | ~ spl3_51
    | ~ spl3_52 ),
    inference(backward_demodulation,[],[f314,f328])).

fof(f328,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_43
    | ~ spl3_44
    | ~ spl3_51
    | ~ spl3_52 ),
    inference(subsumption_resolution,[],[f327,f67])).

fof(f327,plain,
    ( ~ v2_funct_1(sK2)
    | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | ~ spl3_1
    | ~ spl3_43
    | ~ spl3_44
    | ~ spl3_51
    | ~ spl3_52 ),
    inference(subsumption_resolution,[],[f326,f63])).

fof(f326,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | ~ spl3_43
    | ~ spl3_44
    | ~ spl3_51
    | ~ spl3_52 ),
    inference(subsumption_resolution,[],[f325,f282])).

fof(f325,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | ~ spl3_43
    | ~ spl3_51
    | ~ spl3_52 ),
    inference(subsumption_resolution,[],[f324,f278])).

fof(f324,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | ~ spl3_51
    | ~ spl3_52 ),
    inference(trivial_inequality_removal,[],[f323])).

fof(f323,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | ~ spl3_51
    | ~ spl3_52 ),
    inference(superposition,[],[f321,f317])).

fof(f317,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f316])).

fof(f321,plain,
    ( ! [X2,X0,X1] :
        ( k2_relset_1(X0,X1,X2) != X1
        | ~ v1_funct_2(X2,X0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | ~ v2_funct_1(X2)
        | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) )
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f320])).

fof(f314,plain,
    ( m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_1
    | ~ spl3_43
    | ~ spl3_44
    | ~ spl3_50 ),
    inference(subsumption_resolution,[],[f313,f63])).

fof(f313,plain,
    ( ~ v1_funct_1(sK2)
    | m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_43
    | ~ spl3_44
    | ~ spl3_50 ),
    inference(subsumption_resolution,[],[f312,f278])).

fof(f312,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_44
    | ~ spl3_50 ),
    inference(resolution,[],[f310,f282])).

fof(f310,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(X2,X0,X1)
        | ~ v1_funct_1(X2)
        | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f309])).

fof(f347,plain,
    ( spl3_56
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_43
    | ~ spl3_44
    | ~ spl3_51
    | ~ spl3_52 ),
    inference(avatar_split_clause,[],[f328,f320,f316,f281,f277,f66,f62,f345])).

fof(f339,plain,
    ( ~ spl3_54
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_43
    | ~ spl3_44
    | spl3_45
    | ~ spl3_51
    | ~ spl3_52 ),
    inference(avatar_split_clause,[],[f331,f320,f316,f290,f281,f277,f66,f62,f337])).

fof(f290,plain,
    ( spl3_45
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f331,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_43
    | ~ spl3_44
    | spl3_45
    | ~ spl3_51
    | ~ spl3_52 ),
    inference(backward_demodulation,[],[f291,f328])).

fof(f291,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | spl3_45 ),
    inference(avatar_component_clause,[],[f290])).

fof(f335,plain,
    ( ~ spl3_53
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_43
    | ~ spl3_44
    | spl3_47
    | ~ spl3_51
    | ~ spl3_52 ),
    inference(avatar_split_clause,[],[f330,f320,f316,f298,f281,f277,f66,f62,f333])).

fof(f330,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_1
    | ~ spl3_2
    | ~ spl3_43
    | ~ spl3_44
    | spl3_47
    | ~ spl3_51
    | ~ spl3_52 ),
    inference(backward_demodulation,[],[f299,f328])).

fof(f322,plain,(
    spl3_52 ),
    inference(avatar_split_clause,[],[f55,f320])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( k2_tops_2(X0,X1,X2) = k2_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_tops_2(X0,X1,X2) = k2_funct_1(X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f318,plain,
    ( spl3_51
    | ~ spl3_32
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f273,f254,f212,f316])).

fof(f212,plain,
    ( spl3_32
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f254,plain,
    ( spl3_42
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f273,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_32
    | ~ spl3_42 ),
    inference(backward_demodulation,[],[f213,f255])).

fof(f255,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f254])).

fof(f213,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f212])).

fof(f311,plain,(
    spl3_50 ),
    inference(avatar_split_clause,[],[f54,f309])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f300,plain,
    ( ~ spl3_47
    | spl3_31
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f272,f254,f208,f298])).

fof(f208,plain,
    ( spl3_31
  <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f272,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | spl3_31
    | ~ spl3_42 ),
    inference(backward_demodulation,[],[f209,f255])).

fof(f209,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl3_31 ),
    inference(avatar_component_clause,[],[f208])).

fof(f292,plain,
    ( ~ spl3_45
    | spl3_29
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f271,f254,f200,f290])).

fof(f200,plain,
    ( spl3_29
  <=> k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f271,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | spl3_29
    | ~ spl3_42 ),
    inference(backward_demodulation,[],[f201,f255])).

fof(f201,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl3_29 ),
    inference(avatar_component_clause,[],[f200])).

fof(f283,plain,
    ( spl3_44
    | ~ spl3_28
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f270,f254,f194,f281])).

fof(f194,plain,
    ( spl3_28
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f270,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_28
    | ~ spl3_42 ),
    inference(backward_demodulation,[],[f195,f255])).

fof(f195,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f194])).

fof(f279,plain,
    ( spl3_43
    | ~ spl3_27
    | ~ spl3_42 ),
    inference(avatar_split_clause,[],[f269,f254,f190,f277])).

fof(f190,plain,
    ( spl3_27
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f269,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_27
    | ~ spl3_42 ),
    inference(backward_demodulation,[],[f191,f255])).

fof(f191,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f190])).

fof(f267,plain,
    ( ~ spl3_7
    | spl3_26
    | ~ spl3_41 ),
    inference(avatar_contradiction_clause,[],[f266])).

fof(f266,plain,
    ( $false
    | ~ spl3_7
    | spl3_26
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f258,f87])).

fof(f87,plain,
    ( v1_xboole_0(k1_xboole_0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f86])).

fof(f86,plain,
    ( spl3_7
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f258,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_26
    | ~ spl3_41 ),
    inference(backward_demodulation,[],[f187,f252])).

fof(f252,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f251])).

fof(f187,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f186])).

fof(f186,plain,
    ( spl3_26
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f256,plain,
    ( spl3_41
    | spl3_42
    | ~ spl3_27
    | ~ spl3_28
    | ~ spl3_36
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f249,f240,f228,f194,f190,f254,f251])).

fof(f228,plain,
    ( spl3_36
  <=> k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f249,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl3_27
    | ~ spl3_28
    | ~ spl3_36
    | ~ spl3_39 ),
    inference(forward_demodulation,[],[f248,f229])).

fof(f229,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f228])).

fof(f248,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_27
    | ~ spl3_28
    | ~ spl3_39 ),
    inference(subsumption_resolution,[],[f247,f191])).

fof(f247,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_28
    | ~ spl3_39 ),
    inference(resolution,[],[f241,f195])).

fof(f246,plain,(
    spl3_40 ),
    inference(avatar_split_clause,[],[f53,f244])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f242,plain,(
    spl3_39 ),
    inference(avatar_split_clause,[],[f51,f240])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
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
    inference(flattening,[],[f23])).

fof(f23,plain,(
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
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).

fof(f230,plain,
    ( spl3_36
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f176,f161,f157,f134,f126,f228])).

fof(f126,plain,
    ( spl3_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f134,plain,
    ( spl3_16
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f176,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_22
    | ~ spl3_23 ),
    inference(backward_demodulation,[],[f168,f170])).

fof(f170,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_23 ),
    inference(backward_demodulation,[],[f135,f169])).

fof(f169,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_14
    | ~ spl3_23 ),
    inference(resolution,[],[f162,f127])).

fof(f127,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f126])).

fof(f135,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f134])).

fof(f168,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2)
    | ~ spl3_14
    | ~ spl3_22 ),
    inference(resolution,[],[f158,f127])).

fof(f226,plain,(
    spl3_35 ),
    inference(avatar_split_clause,[],[f58,f224])).

fof(f58,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,k1_xboole_0) ) ),
    inference(equality_resolution,[],[f47])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_xboole_0 != X1
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f214,plain,
    ( spl3_32
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f177,f161,f134,f126,f212])).

fof(f177,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_23 ),
    inference(backward_demodulation,[],[f169,f170])).

fof(f210,plain,
    ( ~ spl3_31
    | ~ spl3_14
    | ~ spl3_16
    | spl3_19
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f175,f161,f145,f134,f126,f208])).

fof(f145,plain,
    ( spl3_19
  <=> k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f175,plain,
    ( k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | ~ spl3_14
    | ~ spl3_16
    | spl3_19
    | ~ spl3_23 ),
    inference(backward_demodulation,[],[f146,f170])).

fof(f146,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_19 ),
    inference(avatar_component_clause,[],[f145])).

fof(f202,plain,
    ( ~ spl3_29
    | ~ spl3_14
    | ~ spl3_16
    | spl3_18
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f174,f161,f142,f134,f126,f200])).

fof(f142,plain,
    ( spl3_18
  <=> k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f174,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | ~ spl3_14
    | ~ spl3_16
    | spl3_18
    | ~ spl3_23 ),
    inference(backward_demodulation,[],[f143,f170])).

fof(f143,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f142])).

fof(f196,plain,
    ( spl3_28
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f172,f161,f134,f126,f194])).

fof(f172,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_23 ),
    inference(backward_demodulation,[],[f127,f170])).

fof(f192,plain,
    ( spl3_27
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f171,f161,f134,f126,f122,f190])).

fof(f122,plain,
    ( spl3_13
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f171,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_23 ),
    inference(backward_demodulation,[],[f123,f170])).

fof(f123,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f122])).

fof(f188,plain,
    ( ~ spl3_26
    | spl3_3
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f184,f179,f102,f74,f70,f186])).

fof(f70,plain,
    ( spl3_3
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f74,plain,
    ( spl3_4
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f102,plain,
    ( spl3_11
  <=> ! [X0] :
        ( v2_struct_0(X0)
        | ~ l1_struct_0(X0)
        | ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f179,plain,
    ( spl3_25
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f184,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_3
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f183,f71])).

fof(f71,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f70])).

fof(f183,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | v2_struct_0(sK1)
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_25 ),
    inference(subsumption_resolution,[],[f182,f75])).

fof(f75,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f74])).

fof(f182,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_11
    | ~ spl3_25 ),
    inference(superposition,[],[f103,f180])).

fof(f180,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f179])).

fof(f103,plain,
    ( ! [X0] :
        ( ~ v1_xboole_0(k2_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_struct_0(X0) )
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f102])).

fof(f181,plain,
    ( spl3_25
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f170,f161,f134,f126,f179])).

fof(f163,plain,(
    spl3_23 ),
    inference(avatar_split_clause,[],[f45,f161])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f159,plain,(
    spl3_22 ),
    inference(avatar_split_clause,[],[f44,f157])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

% (6441)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f155,plain,(
    spl3_21 ),
    inference(avatar_split_clause,[],[f42,f153])).

fof(f42,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f151,plain,(
    spl3_20 ),
    inference(avatar_split_clause,[],[f41,f149])).

% (6445)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f41,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f147,plain,
    ( ~ spl3_18
    | ~ spl3_19
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f120,f98,f78,f74,f145,f142])).

fof(f78,plain,
    ( spl3_5
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f98,plain,
    ( spl3_10
  <=> ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f120,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f116,f110])).

fof(f110,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(resolution,[],[f99,f79])).

fof(f79,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f78])).

fof(f99,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X0) = u1_struct_0(X0) )
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f98])).

fof(f116,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f115,f110])).

fof(f115,plain,
    ( k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f114,f109])).

fof(f109,plain,
    ( k2_struct_0(sK1) = u1_struct_0(sK1)
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(resolution,[],[f99,f75])).

fof(f114,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f29,f109])).

fof(f29,plain,
    ( k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
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
    inference(flattening,[],[f13])).

fof(f13,plain,(
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
    inference(ennf_transformation,[],[f12])).

% (6459)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f12,negated_conjecture,(
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
    inference(negated_conjecture,[],[f11])).

fof(f11,conjecture,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).

fof(f136,plain,
    ( spl3_16
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f119,f98,f94,f78,f74,f134])).

fof(f94,plain,
    ( spl3_9
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f119,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f111,f110])).

fof(f111,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f95,f109])).

fof(f95,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f94])).

fof(f128,plain,
    ( spl3_14
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f118,f98,f90,f78,f74,f126])).

fof(f90,plain,
    ( spl3_8
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f118,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f112,f110])).

fof(f112,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f91,f109])).

fof(f91,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f90])).

fof(f124,plain,
    ( spl3_13
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f117,f98,f82,f78,f74,f122])).

fof(f82,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f117,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f113,f110])).

fof(f113,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_4
    | ~ spl3_6
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f83,f109])).

fof(f83,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f82])).

fof(f108,plain,(
    spl3_12 ),
    inference(avatar_split_clause,[],[f43,f106])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f104,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f40,f102])).

fof(f40,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f100,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f39,f98])).

fof(f39,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f96,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f33,f94])).

fof(f33,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f92,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f32,f90])).

fof(f32,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f14])).

fof(f88,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f38,f86])).

fof(f38,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f84,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f31,f82])).

fof(f31,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f14])).

fof(f80,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f37,f78])).

fof(f37,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f14])).

fof(f76,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f36,f74])).

fof(f36,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f72,plain,(
    ~ spl3_3 ),
    inference(avatar_split_clause,[],[f35,f70])).

fof(f35,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f14])).

fof(f68,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f34,f66])).

fof(f34,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).

fof(f64,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f30,f62])).

fof(f30,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f14])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : run_vampire %s %d
% 0.14/0.33  % Computer   : n021.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % WCLimit    : 600
% 0.14/0.33  % DateTime   : Tue Dec  1 10:09:49 EST 2020
% 0.14/0.33  % CPUTime    : 
% 0.20/0.44  % (6443)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.45  % (6450)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.46  % (6450)Refutation found. Thanks to Tanya!
% 0.20/0.46  % SZS status Theorem for theBenchmark
% 0.20/0.46  % (6458)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.47  % SZS output start Proof for theBenchmark
% 0.20/0.47  fof(f607,plain,(
% 0.20/0.47    $false),
% 0.20/0.47    inference(avatar_sat_refutation,[],[f64,f68,f72,f76,f80,f84,f88,f92,f96,f100,f104,f108,f124,f128,f136,f147,f151,f155,f159,f163,f181,f188,f192,f196,f202,f210,f214,f226,f230,f242,f246,f256,f267,f279,f283,f292,f300,f311,f318,f322,f335,f339,f347,f351,f368,f378,f383,f390,f392,f445,f448,f472,f524,f552,f606])).
% 0.20/0.47  fof(f606,plain,(
% 0.20/0.47    ~spl3_66 | ~spl3_1 | ~spl3_2 | ~spl3_20 | spl3_64 | ~spl3_77),
% 0.20/0.47    inference(avatar_split_clause,[],[f584,f550,f402,f149,f66,f62,f443])).
% 0.20/0.47  fof(f443,plain,(
% 0.20/0.47    spl3_66 <=> v1_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 0.20/0.47  fof(f62,plain,(
% 0.20/0.47    spl3_1 <=> v1_funct_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.47  fof(f66,plain,(
% 0.20/0.47    spl3_2 <=> v2_funct_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.47  fof(f149,plain,(
% 0.20/0.47    spl3_20 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.20/0.47  fof(f402,plain,(
% 0.20/0.47    spl3_64 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 0.20/0.47  fof(f550,plain,(
% 0.20/0.47    spl3_77 <=> k1_xboole_0 = k2_funct_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).
% 0.20/0.47  fof(f584,plain,(
% 0.20/0.47    ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_2 | ~spl3_20 | spl3_64 | ~spl3_77)),
% 0.20/0.47    inference(subsumption_resolution,[],[f583,f67])).
% 0.20/0.47  fof(f67,plain,(
% 0.20/0.47    v2_funct_1(sK2) | ~spl3_2),
% 0.20/0.47    inference(avatar_component_clause,[],[f66])).
% 0.20/0.47  fof(f583,plain,(
% 0.20/0.47    ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_20 | spl3_64 | ~spl3_77)),
% 0.20/0.47    inference(subsumption_resolution,[],[f582,f63])).
% 0.20/0.47  fof(f63,plain,(
% 0.20/0.47    v1_funct_1(sK2) | ~spl3_1),
% 0.20/0.47    inference(avatar_component_clause,[],[f62])).
% 0.20/0.47  fof(f582,plain,(
% 0.20/0.47    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_20 | spl3_64 | ~spl3_77)),
% 0.20/0.47    inference(subsumption_resolution,[],[f578,f562])).
% 0.20/0.47  fof(f562,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k1_relat_1(k1_xboole_0) | (spl3_64 | ~spl3_77)),
% 0.20/0.47    inference(backward_demodulation,[],[f547,f551])).
% 0.20/0.47  fof(f551,plain,(
% 0.20/0.47    k1_xboole_0 = k2_funct_1(sK2) | ~spl3_77),
% 0.20/0.47    inference(avatar_component_clause,[],[f550])).
% 0.20/0.47  fof(f547,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | spl3_64),
% 0.20/0.47    inference(avatar_component_clause,[],[f402])).
% 0.20/0.47  fof(f578,plain,(
% 0.20/0.47    k2_relat_1(sK2) = k1_relat_1(k1_xboole_0) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_20 | ~spl3_77)),
% 0.20/0.47    inference(superposition,[],[f150,f551])).
% 0.20/0.47  fof(f150,plain,(
% 0.20/0.47    ( ! [X0] : (k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_20),
% 0.20/0.47    inference(avatar_component_clause,[],[f149])).
% 0.20/0.47  fof(f552,plain,(
% 0.20/0.47    spl3_77 | spl3_41 | ~spl3_1 | ~spl3_35 | ~spl3_40 | ~spl3_43 | ~spl3_44 | ~spl3_56 | ~spl3_63 | ~spl3_73),
% 0.20/0.47    inference(avatar_split_clause,[],[f530,f522,f388,f345,f281,f277,f244,f224,f62,f251,f550])).
% 0.20/0.47  fof(f251,plain,(
% 0.20/0.47    spl3_41 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.20/0.47  fof(f224,plain,(
% 0.20/0.47    spl3_35 <=> ! [X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.20/0.47  fof(f244,plain,(
% 0.20/0.47    spl3_40 <=> ! [X1,X0,X2] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.20/0.47  fof(f277,plain,(
% 0.20/0.47    spl3_43 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.20/0.47  fof(f281,plain,(
% 0.20/0.47    spl3_44 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.20/0.47  fof(f345,plain,(
% 0.20/0.47    spl3_56 <=> k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.20/0.47  fof(f388,plain,(
% 0.20/0.47    spl3_63 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).
% 0.20/0.47  fof(f522,plain,(
% 0.20/0.47    spl3_73 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_xboole_0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_73])])).
% 0.20/0.47  fof(f530,plain,(
% 0.20/0.47    k1_xboole_0 = k2_relat_1(sK2) | k1_xboole_0 = k2_funct_1(sK2) | (~spl3_1 | ~spl3_35 | ~spl3_40 | ~spl3_43 | ~spl3_44 | ~spl3_56 | ~spl3_63 | ~spl3_73)),
% 0.20/0.47    inference(subsumption_resolution,[],[f525,f460])).
% 0.20/0.47  fof(f460,plain,(
% 0.20/0.47    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_xboole_0) | (~spl3_1 | ~spl3_40 | ~spl3_43 | ~spl3_44 | ~spl3_56 | ~spl3_63)),
% 0.20/0.47    inference(backward_demodulation,[],[f361,f389])).
% 0.20/0.47  fof(f389,plain,(
% 0.20/0.47    k1_xboole_0 = k1_relat_1(sK2) | ~spl3_63),
% 0.20/0.47    inference(avatar_component_clause,[],[f388])).
% 0.20/0.47  fof(f361,plain,(
% 0.20/0.47    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | (~spl3_1 | ~spl3_40 | ~spl3_43 | ~spl3_44 | ~spl3_56)),
% 0.20/0.47    inference(subsumption_resolution,[],[f360,f63])).
% 0.20/0.47  fof(f360,plain,(
% 0.20/0.47    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_40 | ~spl3_43 | ~spl3_44 | ~spl3_56)),
% 0.20/0.47    inference(subsumption_resolution,[],[f359,f282])).
% 0.20/0.47  fof(f282,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_44),
% 0.20/0.47    inference(avatar_component_clause,[],[f281])).
% 0.20/0.47  fof(f359,plain,(
% 0.20/0.47    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(sK2) | (~spl3_40 | ~spl3_43 | ~spl3_56)),
% 0.20/0.47    inference(subsumption_resolution,[],[f357,f278])).
% 0.20/0.47  fof(f278,plain,(
% 0.20/0.47    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_43),
% 0.20/0.47    inference(avatar_component_clause,[],[f277])).
% 0.20/0.47  fof(f357,plain,(
% 0.20/0.47    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(sK2) | (~spl3_40 | ~spl3_56)),
% 0.20/0.47    inference(superposition,[],[f245,f346])).
% 0.20/0.47  fof(f346,plain,(
% 0.20/0.47    k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) | ~spl3_56),
% 0.20/0.47    inference(avatar_component_clause,[],[f345])).
% 0.20/0.47  fof(f245,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | ~spl3_40),
% 0.20/0.47    inference(avatar_component_clause,[],[f244])).
% 0.20/0.47  fof(f525,plain,(
% 0.20/0.47    k1_xboole_0 = k2_relat_1(sK2) | k1_xboole_0 = k2_funct_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_xboole_0) | (~spl3_35 | ~spl3_73)),
% 0.20/0.47    inference(resolution,[],[f523,f225])).
% 0.20/0.47  fof(f225,plain,(
% 0.20/0.47    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) ) | ~spl3_35),
% 0.20/0.47    inference(avatar_component_clause,[],[f224])).
% 0.20/0.47  fof(f523,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_xboole_0))) | ~spl3_73),
% 0.20/0.47    inference(avatar_component_clause,[],[f522])).
% 0.20/0.47  fof(f524,plain,(
% 0.20/0.47    spl3_73 | ~spl3_57 | ~spl3_63),
% 0.20/0.47    inference(avatar_split_clause,[],[f459,f388,f349,f522])).
% 0.20/0.47  fof(f349,plain,(
% 0.20/0.47    spl3_57 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 0.20/0.47  fof(f459,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_xboole_0))) | (~spl3_57 | ~spl3_63)),
% 0.20/0.47    inference(backward_demodulation,[],[f350,f389])).
% 0.20/0.47  fof(f350,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_57),
% 0.20/0.47    inference(avatar_component_clause,[],[f349])).
% 0.20/0.47  fof(f472,plain,(
% 0.20/0.47    spl3_47 | ~spl3_56 | ~spl3_60 | ~spl3_63 | ~spl3_64),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f471])).
% 0.20/0.47  fof(f471,plain,(
% 0.20/0.47    $false | (spl3_47 | ~spl3_56 | ~spl3_60 | ~spl3_63 | ~spl3_64)),
% 0.20/0.47    inference(subsumption_resolution,[],[f470,f463])).
% 0.20/0.47  fof(f463,plain,(
% 0.20/0.47    k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_xboole_0,k2_funct_1(sK2)) | (~spl3_60 | ~spl3_63 | ~spl3_64)),
% 0.20/0.47    inference(backward_demodulation,[],[f431,f389])).
% 0.20/0.47  fof(f431,plain,(
% 0.20/0.47    k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_60 | ~spl3_64)),
% 0.20/0.47    inference(backward_demodulation,[],[f377,f403])).
% 0.20/0.47  fof(f403,plain,(
% 0.20/0.47    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_64),
% 0.20/0.47    inference(avatar_component_clause,[],[f402])).
% 0.20/0.47  fof(f377,plain,(
% 0.20/0.47    k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_60),
% 0.20/0.47    inference(avatar_component_clause,[],[f376])).
% 0.20/0.47  fof(f376,plain,(
% 0.20/0.47    spl3_60 <=> k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_60])])).
% 0.20/0.47  fof(f470,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_xboole_0,k2_funct_1(sK2)) | (spl3_47 | ~spl3_56 | ~spl3_63)),
% 0.20/0.47    inference(forward_demodulation,[],[f469,f458])).
% 0.20/0.47  fof(f458,plain,(
% 0.20/0.47    k2_funct_1(sK2) = k2_tops_2(k1_xboole_0,k2_relat_1(sK2),sK2) | (~spl3_56 | ~spl3_63)),
% 0.20/0.47    inference(backward_demodulation,[],[f346,f389])).
% 0.20/0.47  fof(f469,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_xboole_0,k2_tops_2(k1_xboole_0,k2_relat_1(sK2),sK2)) | (spl3_47 | ~spl3_63)),
% 0.20/0.47    inference(forward_demodulation,[],[f299,f389])).
% 0.20/0.47  fof(f299,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | spl3_47),
% 0.20/0.47    inference(avatar_component_clause,[],[f298])).
% 0.20/0.47  fof(f298,plain,(
% 0.20/0.47    spl3_47 <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.20/0.47  fof(f448,plain,(
% 0.20/0.47    ~spl3_12 | ~spl3_44 | spl3_66),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f446])).
% 0.20/0.47  fof(f446,plain,(
% 0.20/0.47    $false | (~spl3_12 | ~spl3_44 | spl3_66)),
% 0.20/0.47    inference(unit_resulting_resolution,[],[f282,f444,f107])).
% 0.20/0.47  fof(f107,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | ~spl3_12),
% 0.20/0.47    inference(avatar_component_clause,[],[f106])).
% 0.20/0.47  fof(f106,plain,(
% 0.20/0.47    spl3_12 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.47  fof(f444,plain,(
% 0.20/0.47    ~v1_relat_1(sK2) | spl3_66),
% 0.20/0.47    inference(avatar_component_clause,[],[f443])).
% 0.20/0.47  fof(f445,plain,(
% 0.20/0.47    ~spl3_66 | ~spl3_1 | ~spl3_2 | ~spl3_21 | spl3_61),
% 0.20/0.47    inference(avatar_split_clause,[],[f400,f381,f153,f66,f62,f443])).
% 0.20/0.47  fof(f153,plain,(
% 0.20/0.47    spl3_21 <=> ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.47  fof(f381,plain,(
% 0.20/0.47    spl3_61 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 0.20/0.47  fof(f400,plain,(
% 0.20/0.47    ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_2 | ~spl3_21 | spl3_61)),
% 0.20/0.47    inference(subsumption_resolution,[],[f399,f67])).
% 0.20/0.47  fof(f399,plain,(
% 0.20/0.47    ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_1 | ~spl3_21 | spl3_61)),
% 0.20/0.47    inference(subsumption_resolution,[],[f398,f63])).
% 0.20/0.47  fof(f398,plain,(
% 0.20/0.47    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_21 | spl3_61)),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f397])).
% 0.20/0.47  fof(f397,plain,(
% 0.20/0.47    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_21 | spl3_61)),
% 0.20/0.47    inference(superposition,[],[f382,f154])).
% 0.20/0.47  fof(f154,plain,(
% 0.20/0.47    ( ! [X0] : (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | ~v1_relat_1(X0)) ) | ~spl3_21),
% 0.20/0.47    inference(avatar_component_clause,[],[f153])).
% 0.20/0.47  fof(f382,plain,(
% 0.20/0.47    k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | spl3_61),
% 0.20/0.47    inference(avatar_component_clause,[],[f381])).
% 0.20/0.47  fof(f392,plain,(
% 0.20/0.47    ~spl3_1 | ~spl3_40 | ~spl3_43 | ~spl3_44 | ~spl3_56 | spl3_62),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f391])).
% 0.20/0.47  fof(f391,plain,(
% 0.20/0.47    $false | (~spl3_1 | ~spl3_40 | ~spl3_43 | ~spl3_44 | ~spl3_56 | spl3_62)),
% 0.20/0.47    inference(subsumption_resolution,[],[f386,f361])).
% 0.20/0.47  fof(f386,plain,(
% 0.20/0.47    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | spl3_62),
% 0.20/0.47    inference(avatar_component_clause,[],[f385])).
% 0.20/0.47  fof(f385,plain,(
% 0.20/0.47    spl3_62 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 0.20/0.47  fof(f390,plain,(
% 0.20/0.47    ~spl3_62 | spl3_63 | ~spl3_39 | spl3_53 | ~spl3_57),
% 0.20/0.47    inference(avatar_split_clause,[],[f356,f349,f333,f240,f388,f385])).
% 0.20/0.47  fof(f240,plain,(
% 0.20/0.47    spl3_39 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.20/0.47  fof(f333,plain,(
% 0.20/0.47    spl3_53 <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 0.20/0.47  fof(f356,plain,(
% 0.20/0.47    k1_xboole_0 = k1_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | (~spl3_39 | spl3_53 | ~spl3_57)),
% 0.20/0.47    inference(subsumption_resolution,[],[f353,f334])).
% 0.20/0.47  fof(f334,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | spl3_53),
% 0.20/0.47    inference(avatar_component_clause,[],[f333])).
% 0.20/0.47  fof(f353,plain,(
% 0.20/0.47    k1_xboole_0 = k1_relat_1(sK2) | k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | (~spl3_39 | ~spl3_57)),
% 0.20/0.47    inference(resolution,[],[f350,f241])).
% 0.20/0.47  fof(f241,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) ) | ~spl3_39),
% 0.20/0.47    inference(avatar_component_clause,[],[f240])).
% 0.20/0.47  fof(f383,plain,(
% 0.20/0.47    ~spl3_61 | spl3_54 | ~spl3_58),
% 0.20/0.47    inference(avatar_split_clause,[],[f373,f366,f337,f381])).
% 0.20/0.47  fof(f337,plain,(
% 0.20/0.47    spl3_54 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.20/0.47  fof(f366,plain,(
% 0.20/0.47    spl3_58 <=> k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 0.20/0.47  fof(f373,plain,(
% 0.20/0.47    k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | (spl3_54 | ~spl3_58)),
% 0.20/0.47    inference(superposition,[],[f338,f367])).
% 0.20/0.47  fof(f367,plain,(
% 0.20/0.47    k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_58),
% 0.20/0.47    inference(avatar_component_clause,[],[f366])).
% 0.20/0.47  fof(f338,plain,(
% 0.20/0.47    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | spl3_54),
% 0.20/0.47    inference(avatar_component_clause,[],[f337])).
% 0.20/0.47  fof(f378,plain,(
% 0.20/0.47    spl3_60 | ~spl3_22 | ~spl3_57),
% 0.20/0.47    inference(avatar_split_clause,[],[f355,f349,f157,f376])).
% 0.20/0.47  fof(f157,plain,(
% 0.20/0.47    spl3_22 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.47  fof(f355,plain,(
% 0.20/0.47    k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) | (~spl3_22 | ~spl3_57)),
% 0.20/0.47    inference(resolution,[],[f350,f158])).
% 0.20/0.47  fof(f158,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) ) | ~spl3_22),
% 0.20/0.47    inference(avatar_component_clause,[],[f157])).
% 0.20/0.47  fof(f368,plain,(
% 0.20/0.47    spl3_58 | ~spl3_23 | ~spl3_57),
% 0.20/0.47    inference(avatar_split_clause,[],[f354,f349,f161,f366])).
% 0.20/0.47  fof(f161,plain,(
% 0.20/0.47    spl3_23 <=> ! [X1,X0,X2] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.20/0.47  fof(f354,plain,(
% 0.20/0.47    k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_23 | ~spl3_57)),
% 0.20/0.47    inference(resolution,[],[f350,f162])).
% 0.20/0.47  fof(f162,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) ) | ~spl3_23),
% 0.20/0.47    inference(avatar_component_clause,[],[f161])).
% 0.20/0.47  fof(f351,plain,(
% 0.20/0.47    spl3_57 | ~spl3_1 | ~spl3_2 | ~spl3_43 | ~spl3_44 | ~spl3_50 | ~spl3_51 | ~spl3_52),
% 0.20/0.47    inference(avatar_split_clause,[],[f329,f320,f316,f309,f281,f277,f66,f62,f349])).
% 0.20/0.47  fof(f309,plain,(
% 0.20/0.47    spl3_50 <=> ! [X1,X0,X2] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.20/0.47  fof(f316,plain,(
% 0.20/0.47    spl3_51 <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 0.20/0.47  fof(f320,plain,(
% 0.20/0.47    spl3_52 <=> ! [X1,X0,X2] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_tops_2(X0,X1,X2) = k2_funct_1(X2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.20/0.47  fof(f329,plain,(
% 0.20/0.47    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_1 | ~spl3_2 | ~spl3_43 | ~spl3_44 | ~spl3_50 | ~spl3_51 | ~spl3_52)),
% 0.20/0.47    inference(backward_demodulation,[],[f314,f328])).
% 0.20/0.47  fof(f328,plain,(
% 0.20/0.47    k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) | (~spl3_1 | ~spl3_2 | ~spl3_43 | ~spl3_44 | ~spl3_51 | ~spl3_52)),
% 0.20/0.47    inference(subsumption_resolution,[],[f327,f67])).
% 0.20/0.47  fof(f327,plain,(
% 0.20/0.47    ~v2_funct_1(sK2) | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) | (~spl3_1 | ~spl3_43 | ~spl3_44 | ~spl3_51 | ~spl3_52)),
% 0.20/0.47    inference(subsumption_resolution,[],[f326,f63])).
% 0.20/0.47  fof(f326,plain,(
% 0.20/0.47    ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) | (~spl3_43 | ~spl3_44 | ~spl3_51 | ~spl3_52)),
% 0.20/0.47    inference(subsumption_resolution,[],[f325,f282])).
% 0.20/0.47  fof(f325,plain,(
% 0.20/0.47    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) | (~spl3_43 | ~spl3_51 | ~spl3_52)),
% 0.20/0.47    inference(subsumption_resolution,[],[f324,f278])).
% 0.20/0.47  fof(f324,plain,(
% 0.20/0.47    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) | (~spl3_51 | ~spl3_52)),
% 0.20/0.47    inference(trivial_inequality_removal,[],[f323])).
% 0.20/0.47  fof(f323,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(sK2) | ~v2_funct_1(sK2) | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) | (~spl3_51 | ~spl3_52)),
% 0.20/0.47    inference(superposition,[],[f321,f317])).
% 0.20/0.47  fof(f317,plain,(
% 0.20/0.47    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_51),
% 0.20/0.47    inference(avatar_component_clause,[],[f316])).
% 0.20/0.47  fof(f321,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_tops_2(X0,X1,X2) = k2_funct_1(X2)) ) | ~spl3_52),
% 0.20/0.47    inference(avatar_component_clause,[],[f320])).
% 0.20/0.47  fof(f314,plain,(
% 0.20/0.47    m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_1 | ~spl3_43 | ~spl3_44 | ~spl3_50)),
% 0.20/0.47    inference(subsumption_resolution,[],[f313,f63])).
% 0.20/0.47  fof(f313,plain,(
% 0.20/0.47    ~v1_funct_1(sK2) | m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_43 | ~spl3_44 | ~spl3_50)),
% 0.20/0.47    inference(subsumption_resolution,[],[f312,f278])).
% 0.20/0.47  fof(f312,plain,(
% 0.20/0.47    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | m1_subset_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_44 | ~spl3_50)),
% 0.20/0.47    inference(resolution,[],[f310,f282])).
% 0.20/0.47  fof(f310,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | ~spl3_50),
% 0.20/0.47    inference(avatar_component_clause,[],[f309])).
% 0.20/0.47  fof(f347,plain,(
% 0.20/0.47    spl3_56 | ~spl3_1 | ~spl3_2 | ~spl3_43 | ~spl3_44 | ~spl3_51 | ~spl3_52),
% 0.20/0.47    inference(avatar_split_clause,[],[f328,f320,f316,f281,f277,f66,f62,f345])).
% 0.20/0.47  fof(f339,plain,(
% 0.20/0.47    ~spl3_54 | ~spl3_1 | ~spl3_2 | ~spl3_43 | ~spl3_44 | spl3_45 | ~spl3_51 | ~spl3_52),
% 0.20/0.47    inference(avatar_split_clause,[],[f331,f320,f316,f290,f281,f277,f66,f62,f337])).
% 0.20/0.47  fof(f290,plain,(
% 0.20/0.47    spl3_45 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.20/0.47  fof(f331,plain,(
% 0.20/0.47    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_43 | ~spl3_44 | spl3_45 | ~spl3_51 | ~spl3_52)),
% 0.20/0.47    inference(backward_demodulation,[],[f291,f328])).
% 0.20/0.47  fof(f291,plain,(
% 0.20/0.47    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | spl3_45),
% 0.20/0.47    inference(avatar_component_clause,[],[f290])).
% 0.20/0.47  fof(f335,plain,(
% 0.20/0.47    ~spl3_53 | ~spl3_1 | ~spl3_2 | ~spl3_43 | ~spl3_44 | spl3_47 | ~spl3_51 | ~spl3_52),
% 0.20/0.47    inference(avatar_split_clause,[],[f330,f320,f316,f298,f281,f277,f66,f62,f333])).
% 0.20/0.47  fof(f330,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_1 | ~spl3_2 | ~spl3_43 | ~spl3_44 | spl3_47 | ~spl3_51 | ~spl3_52)),
% 0.20/0.47    inference(backward_demodulation,[],[f299,f328])).
% 0.20/0.47  fof(f322,plain,(
% 0.20/0.47    spl3_52),
% 0.20/0.47    inference(avatar_split_clause,[],[f55,f320])).
% 0.20/0.47  fof(f55,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_tops_2(X0,X1,X2) = k2_funct_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f28])).
% 0.20/0.47  fof(f28,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.47    inference(flattening,[],[f27])).
% 0.20/0.47  fof(f27,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((k2_tops_2(X0,X1,X2) = k2_funct_1(X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f9])).
% 0.20/0.47  fof(f9,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_tops_2(X0,X1,X2) = k2_funct_1(X2)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.20/0.47  fof(f318,plain,(
% 0.20/0.47    spl3_51 | ~spl3_32 | ~spl3_42),
% 0.20/0.47    inference(avatar_split_clause,[],[f273,f254,f212,f316])).
% 0.20/0.47  fof(f212,plain,(
% 0.20/0.47    spl3_32 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.20/0.47  fof(f254,plain,(
% 0.20/0.47    spl3_42 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.20/0.47  fof(f273,plain,(
% 0.20/0.47    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_32 | ~spl3_42)),
% 0.20/0.47    inference(backward_demodulation,[],[f213,f255])).
% 0.20/0.47  fof(f255,plain,(
% 0.20/0.47    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_42),
% 0.20/0.47    inference(avatar_component_clause,[],[f254])).
% 0.20/0.47  fof(f213,plain,(
% 0.20/0.47    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_32),
% 0.20/0.47    inference(avatar_component_clause,[],[f212])).
% 0.20/0.47  fof(f311,plain,(
% 0.20/0.47    spl3_50),
% 0.20/0.47    inference(avatar_split_clause,[],[f54,f309])).
% 0.20/0.47  fof(f54,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f26])).
% 0.20/0.47  fof(f26,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.47    inference(flattening,[],[f25])).
% 0.20/0.47  fof(f25,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.47    inference(ennf_transformation,[],[f10])).
% 0.20/0.47  fof(f10,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.20/0.47  fof(f300,plain,(
% 0.20/0.47    ~spl3_47 | spl3_31 | ~spl3_42),
% 0.20/0.47    inference(avatar_split_clause,[],[f272,f254,f208,f298])).
% 0.20/0.47  fof(f208,plain,(
% 0.20/0.47    spl3_31 <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.20/0.47  fof(f272,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | (spl3_31 | ~spl3_42)),
% 0.20/0.47    inference(backward_demodulation,[],[f209,f255])).
% 0.20/0.47  fof(f209,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | spl3_31),
% 0.20/0.47    inference(avatar_component_clause,[],[f208])).
% 0.20/0.47  fof(f292,plain,(
% 0.20/0.47    ~spl3_45 | spl3_29 | ~spl3_42),
% 0.20/0.47    inference(avatar_split_clause,[],[f271,f254,f200,f290])).
% 0.20/0.47  fof(f200,plain,(
% 0.20/0.47    spl3_29 <=> k2_struct_0(sK0) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.20/0.47  fof(f271,plain,(
% 0.20/0.47    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | (spl3_29 | ~spl3_42)),
% 0.20/0.47    inference(backward_demodulation,[],[f201,f255])).
% 0.20/0.47  fof(f201,plain,(
% 0.20/0.47    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | spl3_29),
% 0.20/0.47    inference(avatar_component_clause,[],[f200])).
% 0.20/0.47  fof(f283,plain,(
% 0.20/0.47    spl3_44 | ~spl3_28 | ~spl3_42),
% 0.20/0.47    inference(avatar_split_clause,[],[f270,f254,f194,f281])).
% 0.20/0.47  fof(f194,plain,(
% 0.20/0.47    spl3_28 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.20/0.47  fof(f270,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_28 | ~spl3_42)),
% 0.20/0.47    inference(backward_demodulation,[],[f195,f255])).
% 0.20/0.47  fof(f195,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_28),
% 0.20/0.47    inference(avatar_component_clause,[],[f194])).
% 0.20/0.47  fof(f279,plain,(
% 0.20/0.47    spl3_43 | ~spl3_27 | ~spl3_42),
% 0.20/0.47    inference(avatar_split_clause,[],[f269,f254,f190,f277])).
% 0.20/0.47  fof(f190,plain,(
% 0.20/0.47    spl3_27 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.20/0.47  fof(f269,plain,(
% 0.20/0.47    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_27 | ~spl3_42)),
% 0.20/0.47    inference(backward_demodulation,[],[f191,f255])).
% 0.20/0.47  fof(f191,plain,(
% 0.20/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_27),
% 0.20/0.47    inference(avatar_component_clause,[],[f190])).
% 0.20/0.47  fof(f267,plain,(
% 0.20/0.47    ~spl3_7 | spl3_26 | ~spl3_41),
% 0.20/0.47    inference(avatar_contradiction_clause,[],[f266])).
% 0.20/0.47  fof(f266,plain,(
% 0.20/0.47    $false | (~spl3_7 | spl3_26 | ~spl3_41)),
% 0.20/0.47    inference(subsumption_resolution,[],[f258,f87])).
% 0.20/0.47  fof(f87,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0) | ~spl3_7),
% 0.20/0.47    inference(avatar_component_clause,[],[f86])).
% 0.20/0.47  fof(f86,plain,(
% 0.20/0.47    spl3_7 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.47  fof(f258,plain,(
% 0.20/0.47    ~v1_xboole_0(k1_xboole_0) | (spl3_26 | ~spl3_41)),
% 0.20/0.47    inference(backward_demodulation,[],[f187,f252])).
% 0.20/0.47  fof(f252,plain,(
% 0.20/0.47    k1_xboole_0 = k2_relat_1(sK2) | ~spl3_41),
% 0.20/0.47    inference(avatar_component_clause,[],[f251])).
% 0.20/0.47  fof(f187,plain,(
% 0.20/0.47    ~v1_xboole_0(k2_relat_1(sK2)) | spl3_26),
% 0.20/0.47    inference(avatar_component_clause,[],[f186])).
% 0.20/0.47  fof(f186,plain,(
% 0.20/0.47    spl3_26 <=> v1_xboole_0(k2_relat_1(sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.20/0.47  fof(f256,plain,(
% 0.20/0.47    spl3_41 | spl3_42 | ~spl3_27 | ~spl3_28 | ~spl3_36 | ~spl3_39),
% 0.20/0.47    inference(avatar_split_clause,[],[f249,f240,f228,f194,f190,f254,f251])).
% 0.20/0.47  fof(f228,plain,(
% 0.20/0.47    spl3_36 <=> k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.20/0.47  fof(f249,plain,(
% 0.20/0.47    k2_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2) | (~spl3_27 | ~spl3_28 | ~spl3_36 | ~spl3_39)),
% 0.20/0.47    inference(forward_demodulation,[],[f248,f229])).
% 0.20/0.47  fof(f229,plain,(
% 0.20/0.47    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_36),
% 0.20/0.47    inference(avatar_component_clause,[],[f228])).
% 0.20/0.47  fof(f248,plain,(
% 0.20/0.47    k1_xboole_0 = k2_relat_1(sK2) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_27 | ~spl3_28 | ~spl3_39)),
% 0.20/0.47    inference(subsumption_resolution,[],[f247,f191])).
% 0.20/0.47  fof(f247,plain,(
% 0.20/0.47    k1_xboole_0 = k2_relat_1(sK2) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_28 | ~spl3_39)),
% 0.20/0.47    inference(resolution,[],[f241,f195])).
% 0.20/0.47  fof(f246,plain,(
% 0.20/0.47    spl3_40),
% 0.20/0.47    inference(avatar_split_clause,[],[f53,f244])).
% 0.20/0.47  fof(f53,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f26])).
% 0.20/0.47  fof(f242,plain,(
% 0.20/0.47    spl3_39),
% 0.20/0.47    inference(avatar_split_clause,[],[f51,f240])).
% 0.20/0.47  fof(f51,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f24,plain,(
% 0.20/0.47    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(flattening,[],[f23])).
% 0.20/0.47  fof(f23,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f6])).
% 0.20/0.47  fof(f6,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.47  fof(f230,plain,(
% 0.20/0.47    spl3_36 | ~spl3_14 | ~spl3_16 | ~spl3_22 | ~spl3_23),
% 0.20/0.47    inference(avatar_split_clause,[],[f176,f161,f157,f134,f126,f228])).
% 0.20/0.47  fof(f126,plain,(
% 0.20/0.47    spl3_14 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.47  fof(f134,plain,(
% 0.20/0.47    spl3_16 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.47  fof(f176,plain,(
% 0.20/0.47    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_14 | ~spl3_16 | ~spl3_22 | ~spl3_23)),
% 0.20/0.47    inference(backward_demodulation,[],[f168,f170])).
% 0.20/0.47  fof(f170,plain,(
% 0.20/0.47    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_14 | ~spl3_16 | ~spl3_23)),
% 0.20/0.47    inference(backward_demodulation,[],[f135,f169])).
% 0.20/0.47  fof(f169,plain,(
% 0.20/0.47    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | (~spl3_14 | ~spl3_23)),
% 0.20/0.47    inference(resolution,[],[f162,f127])).
% 0.20/0.47  fof(f127,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_14),
% 0.20/0.47    inference(avatar_component_clause,[],[f126])).
% 0.20/0.47  fof(f135,plain,(
% 0.20/0.47    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_16),
% 0.20/0.47    inference(avatar_component_clause,[],[f134])).
% 0.20/0.47  fof(f168,plain,(
% 0.20/0.47    k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k1_relat_1(sK2) | (~spl3_14 | ~spl3_22)),
% 0.20/0.47    inference(resolution,[],[f158,f127])).
% 0.20/0.47  fof(f226,plain,(
% 0.20/0.47    spl3_35),
% 0.20/0.47    inference(avatar_split_clause,[],[f58,f224])).
% 0.20/0.47  fof(f58,plain,(
% 0.20/0.47    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,k1_xboole_0)) )),
% 0.20/0.47    inference(equality_resolution,[],[f47])).
% 0.20/0.47  fof(f47,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_xboole_0 != X1 | k1_xboole_0 = X0 | k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f24])).
% 0.20/0.47  fof(f214,plain,(
% 0.20/0.47    spl3_32 | ~spl3_14 | ~spl3_16 | ~spl3_23),
% 0.20/0.47    inference(avatar_split_clause,[],[f177,f161,f134,f126,f212])).
% 0.20/0.47  fof(f177,plain,(
% 0.20/0.47    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_14 | ~spl3_16 | ~spl3_23)),
% 0.20/0.47    inference(backward_demodulation,[],[f169,f170])).
% 0.20/0.47  fof(f210,plain,(
% 0.20/0.47    ~spl3_31 | ~spl3_14 | ~spl3_16 | spl3_19 | ~spl3_23),
% 0.20/0.47    inference(avatar_split_clause,[],[f175,f161,f145,f134,f126,f208])).
% 0.20/0.47  fof(f145,plain,(
% 0.20/0.47    spl3_19 <=> k2_struct_0(sK1) = k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.20/0.47  fof(f175,plain,(
% 0.20/0.47    k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | (~spl3_14 | ~spl3_16 | spl3_19 | ~spl3_23)),
% 0.20/0.47    inference(backward_demodulation,[],[f146,f170])).
% 0.20/0.47  fof(f146,plain,(
% 0.20/0.47    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl3_19),
% 0.20/0.47    inference(avatar_component_clause,[],[f145])).
% 0.20/0.47  fof(f202,plain,(
% 0.20/0.47    ~spl3_29 | ~spl3_14 | ~spl3_16 | spl3_18 | ~spl3_23),
% 0.20/0.47    inference(avatar_split_clause,[],[f174,f161,f142,f134,f126,f200])).
% 0.20/0.47  fof(f142,plain,(
% 0.20/0.47    spl3_18 <=> k2_struct_0(sK0) = k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.47  fof(f174,plain,(
% 0.20/0.47    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | (~spl3_14 | ~spl3_16 | spl3_18 | ~spl3_23)),
% 0.20/0.47    inference(backward_demodulation,[],[f143,f170])).
% 0.20/0.47  fof(f143,plain,(
% 0.20/0.47    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | spl3_18),
% 0.20/0.47    inference(avatar_component_clause,[],[f142])).
% 0.20/0.47  fof(f196,plain,(
% 0.20/0.47    spl3_28 | ~spl3_14 | ~spl3_16 | ~spl3_23),
% 0.20/0.47    inference(avatar_split_clause,[],[f172,f161,f134,f126,f194])).
% 0.20/0.47  fof(f172,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_14 | ~spl3_16 | ~spl3_23)),
% 0.20/0.47    inference(backward_demodulation,[],[f127,f170])).
% 0.20/0.47  fof(f192,plain,(
% 0.20/0.47    spl3_27 | ~spl3_13 | ~spl3_14 | ~spl3_16 | ~spl3_23),
% 0.20/0.47    inference(avatar_split_clause,[],[f171,f161,f134,f126,f122,f190])).
% 0.20/0.47  fof(f122,plain,(
% 0.20/0.47    spl3_13 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.47  fof(f171,plain,(
% 0.20/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_13 | ~spl3_14 | ~spl3_16 | ~spl3_23)),
% 0.20/0.47    inference(backward_demodulation,[],[f123,f170])).
% 0.20/0.47  fof(f123,plain,(
% 0.20/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_13),
% 0.20/0.47    inference(avatar_component_clause,[],[f122])).
% 0.20/0.47  fof(f188,plain,(
% 0.20/0.47    ~spl3_26 | spl3_3 | ~spl3_4 | ~spl3_11 | ~spl3_25),
% 0.20/0.47    inference(avatar_split_clause,[],[f184,f179,f102,f74,f70,f186])).
% 0.20/0.47  fof(f70,plain,(
% 0.20/0.47    spl3_3 <=> v2_struct_0(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.47  fof(f74,plain,(
% 0.20/0.47    spl3_4 <=> l1_struct_0(sK1)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.47  fof(f102,plain,(
% 0.20/0.47    spl3_11 <=> ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(k2_struct_0(X0)))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.47  fof(f179,plain,(
% 0.20/0.47    spl3_25 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.20/0.47  fof(f184,plain,(
% 0.20/0.47    ~v1_xboole_0(k2_relat_1(sK2)) | (spl3_3 | ~spl3_4 | ~spl3_11 | ~spl3_25)),
% 0.20/0.47    inference(subsumption_resolution,[],[f183,f71])).
% 0.20/0.47  fof(f71,plain,(
% 0.20/0.47    ~v2_struct_0(sK1) | spl3_3),
% 0.20/0.47    inference(avatar_component_clause,[],[f70])).
% 0.20/0.47  fof(f183,plain,(
% 0.20/0.47    ~v1_xboole_0(k2_relat_1(sK2)) | v2_struct_0(sK1) | (~spl3_4 | ~spl3_11 | ~spl3_25)),
% 0.20/0.47    inference(subsumption_resolution,[],[f182,f75])).
% 0.20/0.47  fof(f75,plain,(
% 0.20/0.47    l1_struct_0(sK1) | ~spl3_4),
% 0.20/0.47    inference(avatar_component_clause,[],[f74])).
% 0.20/0.47  fof(f182,plain,(
% 0.20/0.47    ~v1_xboole_0(k2_relat_1(sK2)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | (~spl3_11 | ~spl3_25)),
% 0.20/0.47    inference(superposition,[],[f103,f180])).
% 0.20/0.47  fof(f180,plain,(
% 0.20/0.47    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_25),
% 0.20/0.47    inference(avatar_component_clause,[],[f179])).
% 0.20/0.47  fof(f103,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) ) | ~spl3_11),
% 0.20/0.47    inference(avatar_component_clause,[],[f102])).
% 0.20/0.47  fof(f181,plain,(
% 0.20/0.47    spl3_25 | ~spl3_14 | ~spl3_16 | ~spl3_23),
% 0.20/0.47    inference(avatar_split_clause,[],[f170,f161,f134,f126,f179])).
% 0.20/0.47  fof(f163,plain,(
% 0.20/0.47    spl3_23),
% 0.20/0.47    inference(avatar_split_clause,[],[f45,f161])).
% 0.20/0.47  fof(f45,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f22])).
% 0.20/0.47  fof(f22,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f5])).
% 0.20/0.47  fof(f5,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.47  fof(f159,plain,(
% 0.20/0.47    spl3_22),
% 0.20/0.47    inference(avatar_split_clause,[],[f44,f157])).
% 0.20/0.47  fof(f44,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f21])).
% 0.20/0.47  fof(f21,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f4])).
% 0.20/0.47  % (6441)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.47  fof(f4,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.47  fof(f155,plain,(
% 0.20/0.47    spl3_21),
% 0.20/0.47    inference(avatar_split_clause,[],[f42,f153])).
% 0.20/0.47  fof(f42,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f19,plain,(
% 0.20/0.47    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.47    inference(flattening,[],[f18])).
% 0.20/0.47  fof(f18,plain,(
% 0.20/0.47    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f2])).
% 0.20/0.47  fof(f2,axiom,(
% 0.20/0.47    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.20/0.47  fof(f151,plain,(
% 0.20/0.47    spl3_20),
% 0.20/0.47    inference(avatar_split_clause,[],[f41,f149])).
% 0.20/0.47  % (6445)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.47  fof(f41,plain,(
% 0.20/0.47    ( ! [X0] : (~v1_relat_1(X0) | ~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f19])).
% 0.20/0.47  fof(f147,plain,(
% 0.20/0.47    ~spl3_18 | ~spl3_19 | ~spl3_4 | ~spl3_5 | ~spl3_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f120,f98,f78,f74,f145,f142])).
% 0.20/0.47  fof(f78,plain,(
% 0.20/0.47    spl3_5 <=> l1_struct_0(sK0)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.47  fof(f98,plain,(
% 0.20/0.47    spl3_10 <=> ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.47  fof(f120,plain,(
% 0.20/0.47    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_10)),
% 0.20/0.47    inference(forward_demodulation,[],[f116,f110])).
% 0.20/0.47  fof(f110,plain,(
% 0.20/0.47    u1_struct_0(sK0) = k2_struct_0(sK0) | (~spl3_5 | ~spl3_10)),
% 0.20/0.47    inference(resolution,[],[f99,f79])).
% 0.20/0.47  fof(f79,plain,(
% 0.20/0.47    l1_struct_0(sK0) | ~spl3_5),
% 0.20/0.47    inference(avatar_component_clause,[],[f78])).
% 0.20/0.47  fof(f99,plain,(
% 0.20/0.47    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) ) | ~spl3_10),
% 0.20/0.47    inference(avatar_component_clause,[],[f98])).
% 0.20/0.47  fof(f116,plain,(
% 0.20/0.47    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_10)),
% 0.20/0.47    inference(backward_demodulation,[],[f115,f110])).
% 0.20/0.47  fof(f115,plain,(
% 0.20/0.47    k2_struct_0(sK1) != k1_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | (~spl3_4 | ~spl3_10)),
% 0.20/0.47    inference(forward_demodulation,[],[f114,f109])).
% 0.20/0.47  fof(f109,plain,(
% 0.20/0.47    k2_struct_0(sK1) = u1_struct_0(sK1) | (~spl3_4 | ~spl3_10)),
% 0.20/0.47    inference(resolution,[],[f99,f75])).
% 0.20/0.47  fof(f114,plain,(
% 0.20/0.47    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | (~spl3_4 | ~spl3_10)),
% 0.20/0.47    inference(backward_demodulation,[],[f29,f109])).
% 0.20/0.47  fof(f29,plain,(
% 0.20/0.47    k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f14,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f13])).
% 0.20/0.47  fof(f13,plain,(
% 0.20/0.47    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f12])).
% 0.20/0.47  % (6459)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.47  fof(f12,negated_conjecture,(
% 0.20/0.47    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.20/0.47    inference(negated_conjecture,[],[f11])).
% 0.20/0.47  fof(f11,conjecture,(
% 0.20/0.47    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 0.20/0.47  fof(f136,plain,(
% 0.20/0.47    spl3_16 | ~spl3_4 | ~spl3_5 | ~spl3_9 | ~spl3_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f119,f98,f94,f78,f74,f134])).
% 0.20/0.47  fof(f94,plain,(
% 0.20/0.47    spl3_9 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.47  fof(f119,plain,(
% 0.20/0.47    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_5 | ~spl3_9 | ~spl3_10)),
% 0.20/0.47    inference(backward_demodulation,[],[f111,f110])).
% 0.20/0.47  fof(f111,plain,(
% 0.20/0.47    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_9 | ~spl3_10)),
% 0.20/0.47    inference(backward_demodulation,[],[f95,f109])).
% 0.20/0.47  fof(f95,plain,(
% 0.20/0.47    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_9),
% 0.20/0.47    inference(avatar_component_clause,[],[f94])).
% 0.20/0.47  fof(f128,plain,(
% 0.20/0.47    spl3_14 | ~spl3_4 | ~spl3_5 | ~spl3_8 | ~spl3_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f118,f98,f90,f78,f74,f126])).
% 0.20/0.47  fof(f90,plain,(
% 0.20/0.47    spl3_8 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.47  fof(f118,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_5 | ~spl3_8 | ~spl3_10)),
% 0.20/0.47    inference(backward_demodulation,[],[f112,f110])).
% 0.20/0.47  fof(f112,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_8 | ~spl3_10)),
% 0.20/0.47    inference(backward_demodulation,[],[f91,f109])).
% 0.20/0.47  fof(f91,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_8),
% 0.20/0.47    inference(avatar_component_clause,[],[f90])).
% 0.20/0.47  fof(f124,plain,(
% 0.20/0.47    spl3_13 | ~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f117,f98,f82,f78,f74,f122])).
% 0.20/0.47  fof(f82,plain,(
% 0.20/0.47    spl3_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.47    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.47  fof(f117,plain,(
% 0.20/0.47    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_4 | ~spl3_5 | ~spl3_6 | ~spl3_10)),
% 0.20/0.47    inference(backward_demodulation,[],[f113,f110])).
% 0.20/0.47  fof(f113,plain,(
% 0.20/0.47    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_4 | ~spl3_6 | ~spl3_10)),
% 0.20/0.47    inference(backward_demodulation,[],[f83,f109])).
% 0.20/0.47  fof(f83,plain,(
% 0.20/0.47    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_6),
% 0.20/0.47    inference(avatar_component_clause,[],[f82])).
% 0.20/0.47  fof(f108,plain,(
% 0.20/0.47    spl3_12),
% 0.20/0.47    inference(avatar_split_clause,[],[f43,f106])).
% 0.20/0.47  fof(f43,plain,(
% 0.20/0.47    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f20])).
% 0.20/0.47  fof(f20,plain,(
% 0.20/0.47    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.47    inference(ennf_transformation,[],[f3])).
% 0.20/0.47  fof(f3,axiom,(
% 0.20/0.47    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.47  fof(f104,plain,(
% 0.20/0.47    spl3_11),
% 0.20/0.47    inference(avatar_split_clause,[],[f40,f102])).
% 0.20/0.47  fof(f40,plain,(
% 0.20/0.47    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(k2_struct_0(X0))) )),
% 0.20/0.47    inference(cnf_transformation,[],[f17])).
% 0.20/0.47  fof(f17,plain,(
% 0.20/0.47    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.47    inference(flattening,[],[f16])).
% 0.20/0.47  fof(f16,plain,(
% 0.20/0.47    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.47    inference(ennf_transformation,[],[f8])).
% 0.20/0.47  fof(f8,axiom,(
% 0.20/0.47    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.20/0.47  fof(f100,plain,(
% 0.20/0.47    spl3_10),
% 0.20/0.47    inference(avatar_split_clause,[],[f39,f98])).
% 0.20/0.47  fof(f39,plain,(
% 0.20/0.47    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.47    inference(cnf_transformation,[],[f15])).
% 0.20/0.47  fof(f15,plain,(
% 0.20/0.47    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.47    inference(ennf_transformation,[],[f7])).
% 0.20/0.47  fof(f7,axiom,(
% 0.20/0.47    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.47  fof(f96,plain,(
% 0.20/0.47    spl3_9),
% 0.20/0.47    inference(avatar_split_clause,[],[f33,f94])).
% 0.20/0.47  fof(f33,plain,(
% 0.20/0.47    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f92,plain,(
% 0.20/0.47    spl3_8),
% 0.20/0.47    inference(avatar_split_clause,[],[f32,f90])).
% 0.20/0.47  fof(f32,plain,(
% 0.20/0.47    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f88,plain,(
% 0.20/0.47    spl3_7),
% 0.20/0.47    inference(avatar_split_clause,[],[f38,f86])).
% 0.20/0.47  fof(f38,plain,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    inference(cnf_transformation,[],[f1])).
% 0.20/0.47  fof(f1,axiom,(
% 0.20/0.47    v1_xboole_0(k1_xboole_0)),
% 0.20/0.47    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.47  fof(f84,plain,(
% 0.20/0.47    spl3_6),
% 0.20/0.47    inference(avatar_split_clause,[],[f31,f82])).
% 0.20/0.47  fof(f31,plain,(
% 0.20/0.47    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f80,plain,(
% 0.20/0.47    spl3_5),
% 0.20/0.47    inference(avatar_split_clause,[],[f37,f78])).
% 0.20/0.47  fof(f37,plain,(
% 0.20/0.47    l1_struct_0(sK0)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f76,plain,(
% 0.20/0.47    spl3_4),
% 0.20/0.47    inference(avatar_split_clause,[],[f36,f74])).
% 0.20/0.47  fof(f36,plain,(
% 0.20/0.47    l1_struct_0(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f72,plain,(
% 0.20/0.47    ~spl3_3),
% 0.20/0.47    inference(avatar_split_clause,[],[f35,f70])).
% 0.20/0.47  fof(f35,plain,(
% 0.20/0.47    ~v2_struct_0(sK1)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f68,plain,(
% 0.20/0.47    spl3_2),
% 0.20/0.47    inference(avatar_split_clause,[],[f34,f66])).
% 0.20/0.47  fof(f34,plain,(
% 0.20/0.47    v2_funct_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  fof(f64,plain,(
% 0.20/0.47    spl3_1),
% 0.20/0.47    inference(avatar_split_clause,[],[f30,f62])).
% 0.20/0.47  fof(f30,plain,(
% 0.20/0.47    v1_funct_1(sK2)),
% 0.20/0.47    inference(cnf_transformation,[],[f14])).
% 0.20/0.47  % SZS output end Proof for theBenchmark
% 0.20/0.48  % (6450)------------------------------
% 0.20/0.48  % (6450)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.48  % (6450)Termination reason: Refutation
% 0.20/0.48  
% 0.20/0.48  % (6450)Memory used [KB]: 10874
% 0.20/0.48  % (6450)Time elapsed: 0.071 s
% 0.20/0.48  % (6450)------------------------------
% 0.20/0.48  % (6450)------------------------------
% 0.20/0.48  % (6440)Success in time 0.13 s
%------------------------------------------------------------------------------
