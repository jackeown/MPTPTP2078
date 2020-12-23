%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:25 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.46s
% Verified   : 
% Statistics : Number of formulae       :  321 ( 809 expanded)
%              Number of leaves         :   71 ( 361 expanded)
%              Depth                    :   11
%              Number of atoms          : 1248 (3029 expanded)
%              Number of equality atoms :  169 ( 456 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f770,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f96,f101,f106,f111,f116,f121,f129,f134,f139,f145,f152,f161,f166,f173,f190,f197,f218,f229,f239,f252,f257,f262,f267,f290,f296,f302,f336,f345,f350,f370,f379,f392,f422,f427,f437,f468,f478,f483,f490,f504,f512,f518,f570,f576,f621,f665,f744,f766,f769])).

fof(f769,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_funct_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | sK2 != k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f766,plain,
    ( ~ spl3_3
    | ~ spl3_23
    | ~ spl3_28
    | ~ spl3_44
    | ~ spl3_46
    | ~ spl3_52
    | ~ spl3_62
    | spl3_69
    | ~ spl3_79 ),
    inference(avatar_contradiction_clause,[],[f765])).

fof(f765,plain,
    ( $false
    | ~ spl3_3
    | ~ spl3_23
    | ~ spl3_28
    | ~ spl3_44
    | ~ spl3_46
    | ~ spl3_52
    | ~ spl3_62
    | spl3_69
    | ~ spl3_79 ),
    inference(subsumption_resolution,[],[f764,f238])).

fof(f238,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f236])).

fof(f236,plain,
    ( spl3_23
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f764,plain,
    ( k2_struct_0(sK1) != k2_relat_1(sK2)
    | ~ spl3_3
    | ~ spl3_28
    | ~ spl3_44
    | ~ spl3_46
    | ~ spl3_52
    | ~ spl3_62
    | spl3_69
    | ~ spl3_79 ),
    inference(forward_demodulation,[],[f763,f482])).

fof(f482,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_52 ),
    inference(avatar_component_clause,[],[f480])).

fof(f480,plain,
    ( spl3_52
  <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f763,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_3
    | ~ spl3_28
    | ~ spl3_44
    | ~ spl3_46
    | ~ spl3_62
    | spl3_69
    | ~ spl3_79 ),
    inference(subsumption_resolution,[],[f762,f660])).

fof(f660,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | spl3_69 ),
    inference(avatar_component_clause,[],[f658])).

fof(f658,plain,
    ( spl3_69
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).

fof(f762,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_3
    | ~ spl3_28
    | ~ spl3_44
    | ~ spl3_46
    | ~ spl3_62
    | ~ spl3_79 ),
    inference(forward_demodulation,[],[f761,f575])).

fof(f575,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_62 ),
    inference(avatar_component_clause,[],[f573])).

fof(f573,plain,
    ( spl3_62
  <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f761,plain,
    ( v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_3
    | ~ spl3_28
    | ~ spl3_44
    | ~ spl3_46
    | ~ spl3_79 ),
    inference(subsumption_resolution,[],[f760,f105])).

fof(f105,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl3_3
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f760,plain,
    ( v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ l1_struct_0(sK1)
    | ~ spl3_28
    | ~ spl3_44
    | ~ spl3_46
    | ~ spl3_79 ),
    inference(subsumption_resolution,[],[f759,f436])).

fof(f436,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f434])).

fof(f434,plain,
    ( spl3_46
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f759,plain,
    ( v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ l1_struct_0(sK1)
    | ~ spl3_28
    | ~ spl3_44
    | ~ spl3_79 ),
    inference(subsumption_resolution,[],[f757,f426])).

fof(f426,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f424])).

fof(f424,plain,
    ( spl3_44
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f757,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ l1_struct_0(sK1)
    | ~ spl3_28
    | ~ spl3_79 ),
    inference(superposition,[],[f743,f266])).

fof(f266,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl3_28
  <=> u1_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f743,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X0))
        | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X0),sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0))))
        | k2_struct_0(X0) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(X0),sK2)
        | ~ l1_struct_0(X0) )
    | ~ spl3_79 ),
    inference(avatar_component_clause,[],[f742])).

fof(f742,plain,
    ( spl3_79
  <=> ! [X0] :
        ( v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X0),sK2))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0))))
        | k2_struct_0(X0) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(X0),sK2)
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_79])])).

fof(f744,plain,
    ( spl3_79
    | ~ spl3_1
    | ~ spl3_49
    | ~ spl3_65 ),
    inference(avatar_split_clause,[],[f630,f619,f465,f93,f742])).

fof(f93,plain,
    ( spl3_1
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f465,plain,
    ( spl3_49
  <=> u1_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f619,plain,
    ( spl3_65
  <=> ! [X1,X0] :
        ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2))
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_struct_0(X1)
        | ~ l1_struct_0(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f630,plain,
    ( ! [X0] :
        ( v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X0),sK2))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0))))
        | k2_struct_0(X0) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(X0),sK2)
        | ~ l1_struct_0(X0) )
    | ~ spl3_1
    | ~ spl3_49
    | ~ spl3_65 ),
    inference(forward_demodulation,[],[f629,f467])).

fof(f467,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f465])).

fof(f629,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0))))
        | k2_struct_0(X0) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(X0),sK2)
        | ~ l1_struct_0(X0)
        | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )
    | ~ spl3_1
    | ~ spl3_49
    | ~ spl3_65 ),
    inference(forward_demodulation,[],[f628,f467])).

fof(f628,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0))))
        | k2_struct_0(X0) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(X0),sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )
    | ~ spl3_1
    | ~ spl3_49
    | ~ spl3_65 ),
    inference(forward_demodulation,[],[f627,f467])).

fof(f627,plain,
    ( ! [X0] :
        ( k2_struct_0(X0) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(X0),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )
    | ~ spl3_1
    | ~ spl3_49
    | ~ spl3_65 ),
    inference(forward_demodulation,[],[f625,f467])).

fof(f625,plain,
    ( ! [X0] :
        ( k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ l1_struct_0(X0)
        | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2)) )
    | ~ spl3_1
    | ~ spl3_65 ),
    inference(resolution,[],[f620,f95])).

fof(f95,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f93])).

fof(f620,plain,
    ( ! [X0,X1] :
        ( ~ l1_struct_0(X0)
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_struct_0(X1)
        | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) )
    | ~ spl3_65 ),
    inference(avatar_component_clause,[],[f619])).

fof(f665,plain,
    ( ~ spl3_69
    | spl3_70
    | ~ spl3_17
    | ~ spl3_33
    | ~ spl3_56
    | ~ spl3_57
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f594,f567,f509,f501,f333,f194,f662,f658])).

fof(f662,plain,
    ( spl3_70
  <=> sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).

fof(f194,plain,
    ( spl3_17
  <=> sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f333,plain,
    ( spl3_33
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f501,plain,
    ( spl3_56
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f509,plain,
    ( spl3_57
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).

fof(f567,plain,
    ( spl3_61
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f594,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_17
    | ~ spl3_33
    | ~ spl3_56
    | ~ spl3_57
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f593,f196])).

fof(f196,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f194])).

fof(f593,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_33
    | ~ spl3_56
    | ~ spl3_57
    | ~ spl3_61 ),
    inference(subsumption_resolution,[],[f592,f335])).

fof(f335,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f333])).

fof(f592,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_56
    | ~ spl3_57
    | ~ spl3_61 ),
    inference(subsumption_resolution,[],[f591,f511])).

fof(f511,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_57 ),
    inference(avatar_component_clause,[],[f509])).

fof(f591,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_56
    | ~ spl3_61 ),
    inference(subsumption_resolution,[],[f590,f503])).

fof(f503,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f501])).

fof(f590,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_61 ),
    inference(trivial_inequality_removal,[],[f583])).

fof(f583,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v2_funct_1(k2_funct_1(sK2))
    | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_61 ),
    inference(superposition,[],[f86,f569])).

fof(f569,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_61 ),
    inference(avatar_component_clause,[],[f567])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f621,plain,
    ( spl3_65
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f331,f113,f108,f619])).

fof(f108,plain,
    ( spl3_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f113,plain,
    ( spl3_5
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f331,plain,
    ( ! [X0,X1] :
        ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2))
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ l1_struct_0(X1)
        | ~ l1_struct_0(X0) )
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f330,f110])).

fof(f110,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f108])).

fof(f330,plain,
    ( ! [X0,X1] :
        ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2))
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(sK2)
        | ~ l1_struct_0(X1)
        | ~ l1_struct_0(X0) )
    | ~ spl3_5 ),
    inference(resolution,[],[f65,f115])).

fof(f115,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f113])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( ( v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
               => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).

fof(f576,plain,
    ( spl3_62
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_44
    | ~ spl3_46
    | ~ spl3_52 ),
    inference(avatar_split_clause,[],[f531,f480,f434,f424,f113,f108,f573])).

fof(f531,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_44
    | ~ spl3_46
    | ~ spl3_52 ),
    inference(subsumption_resolution,[],[f530,f110])).

fof(f530,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_1(sK2)
    | ~ spl3_5
    | ~ spl3_44
    | ~ spl3_46
    | ~ spl3_52 ),
    inference(subsumption_resolution,[],[f529,f426])).

fof(f529,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_5
    | ~ spl3_46
    | ~ spl3_52 ),
    inference(subsumption_resolution,[],[f528,f436])).

fof(f528,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_5
    | ~ spl3_52 ),
    inference(subsumption_resolution,[],[f527,f115])).

fof(f527,plain,
    ( ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_52 ),
    inference(trivial_inequality_removal,[],[f520])).

fof(f520,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_52 ),
    inference(superposition,[],[f86,f482])).

fof(f570,plain,
    ( spl3_61
    | ~ spl3_27
    | ~ spl3_43
    | ~ spl3_51
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f564,f487,f475,f419,f259,f567])).

fof(f259,plain,
    ( spl3_27
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f419,plain,
    ( spl3_43
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f475,plain,
    ( spl3_51
  <=> k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f487,plain,
    ( spl3_53
  <=> k2_funct_1(sK2) = k3_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f564,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_27
    | ~ spl3_43
    | ~ spl3_51
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f563,f477])).

fof(f477,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f475])).

fof(f563,plain,
    ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_27
    | ~ spl3_43
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f562,f489])).

fof(f489,plain,
    ( k2_funct_1(sK2) = k3_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f487])).

fof(f562,plain,
    ( k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k3_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ spl3_27
    | ~ spl3_43 ),
    inference(forward_demodulation,[],[f297,f421])).

fof(f421,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f419])).

fof(f297,plain,
    ( k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | ~ spl3_27 ),
    inference(resolution,[],[f82,f261])).

fof(f261,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f259])).

fof(f82,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1,X2] :
      ( ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))
        & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relset_1)).

fof(f518,plain,
    ( spl3_58
    | ~ spl3_39
    | ~ spl3_44
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f454,f434,f424,f377,f515])).

fof(f515,plain,
    ( spl3_58
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).

fof(f377,plain,
    ( spl3_39
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | r2_funct_2(X0,X1,sK2,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f454,plain,
    ( r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | ~ spl3_39
    | ~ spl3_44
    | ~ spl3_46 ),
    inference(subsumption_resolution,[],[f443,f426])).

fof(f443,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | ~ spl3_39
    | ~ spl3_46 ),
    inference(resolution,[],[f436,f378])).

fof(f378,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | r2_funct_2(X0,X1,sK2,sK2) )
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f377])).

fof(f512,plain,
    ( spl3_57
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_34
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f413,f389,f342,f170,f163,f509])).

fof(f163,plain,
    ( spl3_13
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f170,plain,
    ( spl3_14
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f342,plain,
    ( spl3_34
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f389,plain,
    ( spl3_41
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f413,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_34
    | ~ spl3_41 ),
    inference(backward_demodulation,[],[f344,f397])).

fof(f397,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f396,f165])).

fof(f165,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f163])).

fof(f396,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_14
    | ~ spl3_41 ),
    inference(subsumption_resolution,[],[f395,f172])).

fof(f172,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f170])).

fof(f395,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl3_41 ),
    inference(resolution,[],[f391,f73])).

fof(f73,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f53])).

fof(f53,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f391,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f389])).

fof(f344,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_34 ),
    inference(avatar_component_clause,[],[f342])).

fof(f504,plain,
    ( spl3_56
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_35
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f414,f389,f347,f170,f163,f501])).

fof(f347,plain,
    ( spl3_35
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f414,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_35
    | ~ spl3_41 ),
    inference(backward_demodulation,[],[f349,f397])).

fof(f349,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f347])).

fof(f490,plain,
    ( spl3_53
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_32
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f412,f389,f299,f170,f163,f487])).

fof(f299,plain,
    ( spl3_32
  <=> k2_funct_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f412,plain,
    ( k2_funct_1(sK2) = k3_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_32
    | ~ spl3_41 ),
    inference(backward_demodulation,[],[f301,f397])).

fof(f301,plain,
    ( k2_funct_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f299])).

fof(f483,plain,
    ( spl3_52
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_31
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f411,f389,f293,f170,f163,f480])).

fof(f293,plain,
    ( spl3_31
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f411,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_31
    | ~ spl3_41 ),
    inference(backward_demodulation,[],[f295,f397])).

fof(f295,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f293])).

fof(f478,plain,
    ( spl3_51
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_30
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f410,f389,f287,f170,f163,f475])).

fof(f287,plain,
    ( spl3_30
  <=> k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f410,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_30
    | ~ spl3_41 ),
    inference(backward_demodulation,[],[f289,f397])).

fof(f289,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f287])).

fof(f468,plain,
    ( spl3_49
    | ~ spl3_7
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f405,f389,f170,f163,f126,f465])).

fof(f126,plain,
    ( spl3_7
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f405,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_7
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_41 ),
    inference(backward_demodulation,[],[f128,f397])).

fof(f128,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f126])).

fof(f437,plain,
    ( spl3_46
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_27
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f408,f389,f259,f170,f163,f434])).

fof(f408,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_27
    | ~ spl3_41 ),
    inference(backward_demodulation,[],[f261,f397])).

fof(f427,plain,
    ( spl3_44
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_26
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f407,f389,f254,f170,f163,f424])).

fof(f254,plain,
    ( spl3_26
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f407,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_26
    | ~ spl3_41 ),
    inference(backward_demodulation,[],[f256,f397])).

fof(f256,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f254])).

fof(f422,plain,
    ( spl3_43
    | ~ spl3_13
    | ~ spl3_14
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f397,f389,f170,f163,f419])).

fof(f392,plain,
    ( spl3_41
    | spl3_25
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_37 ),
    inference(avatar_split_clause,[],[f387,f368,f259,f254,f249,f389])).

fof(f249,plain,
    ( spl3_25
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f368,plain,
    ( spl3_37
  <=> ! [X1,X0] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | v1_partfun1(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f387,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | spl3_25
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_37 ),
    inference(subsumption_resolution,[],[f386,f251])).

fof(f251,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_25 ),
    inference(avatar_component_clause,[],[f249])).

fof(f386,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | v1_xboole_0(k2_relat_1(sK2))
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_37 ),
    inference(subsumption_resolution,[],[f385,f256])).

fof(f385,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | v1_xboole_0(k2_relat_1(sK2))
    | ~ spl3_27
    | ~ spl3_37 ),
    inference(resolution,[],[f369,f261])).

fof(f369,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_partfun1(sK2,X0)
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_xboole_0(X1) )
    | ~ spl3_37 ),
    inference(avatar_component_clause,[],[f368])).

fof(f379,plain,
    ( spl3_39
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f285,f108,f377])).

fof(f285,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | r2_funct_2(X0,X1,sK2,sK2) )
    | ~ spl3_4 ),
    inference(resolution,[],[f91,f110])).

fof(f91,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f90])).

fof(f90,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f88])).

fof(f88,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2,X3] :
      ( ( ( r2_funct_2(X0,X1,X2,X3)
          | X2 != X3 )
        & ( X2 = X3
          | ~ r2_funct_2(X0,X1,X2,X3) ) )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(nnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f370,plain,
    ( spl3_37
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f283,f108,f368])).

fof(f283,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_2(sK2,X0,X1)
        | v1_partfun1(sK2,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_xboole_0(X1) )
    | ~ spl3_4 ),
    inference(resolution,[],[f72,f110])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,X0,X1)
      | v1_partfun1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f350,plain,
    ( spl3_35
    | ~ spl3_11
    | ~ spl3_23
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f340,f299,f236,f149,f347])).

fof(f149,plain,
    ( spl3_11
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f340,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_11
    | ~ spl3_23
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f339,f301])).

fof(f339,plain,
    ( m1_subset_1(k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_11
    | ~ spl3_23 ),
    inference(forward_demodulation,[],[f206,f238])).

fof(f206,plain,
    ( m1_subset_1(k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_11 ),
    inference(resolution,[],[f78,f151])).

fof(f151,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f149])).

fof(f78,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).

fof(f345,plain,
    ( spl3_34
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f325,f293,f259,f254,f113,f108,f342])).

fof(f325,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f324,f110])).

fof(f324,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ v1_funct_1(sK2)
    | ~ spl3_5
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f323,f256])).

fof(f323,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_5
    | ~ spl3_27
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f322,f261])).

fof(f322,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_5
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f311,f115])).

fof(f311,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_31 ),
    inference(trivial_inequality_removal,[],[f308])).

fof(f308,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_31 ),
    inference(superposition,[],[f84,f295])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( k2_relset_1(X0,X1,X2) = X1
          & v2_funct_1(X2) )
       => ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
          & v1_funct_2(k2_funct_1(X2),X1,X0)
          & v1_funct_1(k2_funct_1(X2)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).

fof(f336,plain,
    ( spl3_33
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f329,f293,f259,f254,f113,f108,f333])).

fof(f329,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f328,f110])).

fof(f328,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_5
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f327,f256])).

fof(f327,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_5
    | ~ spl3_27
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f326,f261])).

fof(f326,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_5
    | ~ spl3_31 ),
    inference(subsumption_resolution,[],[f310,f115])).

fof(f310,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_31 ),
    inference(trivial_inequality_removal,[],[f309])).

fof(f309,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_31 ),
    inference(superposition,[],[f83,f295])).

fof(f83,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f302,plain,
    ( spl3_32
    | ~ spl3_16
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f275,f259,f187,f299])).

fof(f187,plain,
    ( spl3_16
  <=> k2_funct_1(sK2) = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f275,plain,
    ( k2_funct_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_16
    | ~ spl3_27 ),
    inference(forward_demodulation,[],[f269,f189])).

fof(f189,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f187])).

fof(f269,plain,
    ( k4_relat_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_27 ),
    inference(resolution,[],[f261,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k3_relset_1(X0,X1,X2) = k4_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k3_relset_1(X0,X1,X2) = k4_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).

fof(f296,plain,
    ( spl3_31
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f270,f259,f293])).

fof(f270,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_27 ),
    inference(resolution,[],[f261,f77])).

fof(f77,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f290,plain,
    ( spl3_30
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f268,f259,f287])).

fof(f268,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_27 ),
    inference(resolution,[],[f261,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f267,plain,
    ( spl3_28
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f234,f158,f149,f136,f264])).

fof(f136,plain,
    ( spl3_9
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f158,plain,
    ( spl3_12
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f234,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f138,f224])).

fof(f224,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f160,f201])).

fof(f201,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_11 ),
    inference(resolution,[],[f77,f151])).

fof(f160,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f158])).

fof(f138,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f136])).

fof(f262,plain,
    ( spl3_27
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f232,f158,f149,f259])).

fof(f232,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f151,f224])).

fof(f257,plain,
    ( spl3_26
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f233,f158,f149,f142,f254])).

fof(f142,plain,
    ( spl3_10
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f233,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(backward_demodulation,[],[f144,f224])).

fof(f144,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f142])).

fof(f252,plain,
    ( ~ spl3_25
    | spl3_2
    | ~ spl3_3
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f247,f236,f103,f98,f249])).

fof(f98,plain,
    ( spl3_2
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f247,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_2
    | ~ spl3_3
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f246,f100])).

fof(f100,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f98])).

fof(f246,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | v2_struct_0(sK1)
    | ~ spl3_3
    | ~ spl3_23 ),
    inference(subsumption_resolution,[],[f245,f105])).

fof(f245,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_23 ),
    inference(superposition,[],[f67,f238])).

fof(f67,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(k2_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f239,plain,
    ( spl3_23
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f224,f158,f149,f236])).

fof(f229,plain,
    ( spl3_22
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f201,f149,f226])).

fof(f226,plain,
    ( spl3_22
  <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f218,plain,
    ( ~ spl3_20
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f208,f136,f126,f215])).

fof(f215,plain,
    ( spl3_20
  <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f208,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f207,f128])).

fof(f207,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f63,f138])).

fof(f63,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f51,f50,f49])).

fof(f49,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1)
            & ~ v2_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f50,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2)
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2)
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f51,plain,
    ( ? [X2] :
        ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2)
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f22,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ~ r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,negated_conjecture,(
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
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    inference(negated_conjecture,[],[f19])).

fof(f19,conjecture,(
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
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

fof(f197,plain,
    ( spl3_17
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f185,f163,f113,f108,f194])).

fof(f185,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f184,f165])).

fof(f184,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f183,f110])).

fof(f183,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f69,f115])).

fof(f69,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f190,plain,
    ( spl3_16
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f182,f163,f113,f108,f187])).

fof(f182,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(subsumption_resolution,[],[f181,f165])).

fof(f181,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f180,f110])).

fof(f180,plain,
    ( k2_funct_1(sK2) = k4_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f68,f115])).

fof(f68,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( k2_funct_1(X0) = k4_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(X0) = k4_relat_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).

fof(f173,plain,
    ( spl3_14
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f168,f149,f170])).

fof(f168,plain,
    ( v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ spl3_11 ),
    inference(resolution,[],[f79,f151])).

fof(f79,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v4_relat_1(X2,X0) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
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

fof(f166,plain,
    ( spl3_13
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f156,f149,f163])).

fof(f156,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_11 ),
    inference(resolution,[],[f153,f151])).

fof(f153,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | v1_relat_1(X0) ) ),
    inference(resolution,[],[f66,f70])).

fof(f70,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_relat_1(X0)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).

fof(f161,plain,
    ( spl3_12
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f155,f136,f126,f158])).

fof(f155,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f154,f128])).

fof(f154,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f61,f138])).

fof(f61,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f152,plain,
    ( spl3_11
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f147,f136,f126,f149])).

fof(f147,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_7
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f146,f128])).

fof(f146,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_9 ),
    inference(forward_demodulation,[],[f60,f138])).

fof(f60,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f52])).

fof(f145,plain,
    ( spl3_10
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f140,f136,f131,f142])).

fof(f131,plain,
    ( spl3_8
  <=> v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f140,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_8
    | ~ spl3_9 ),
    inference(backward_demodulation,[],[f133,f138])).

fof(f133,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f131])).

fof(f139,plain,
    ( spl3_9
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f123,f103,f136])).

fof(f123,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f64,f105])).

fof(f64,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f134,plain,
    ( spl3_8
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f124,f118,f93,f131])).

fof(f118,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f124,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_1
    | ~ spl3_6 ),
    inference(backward_demodulation,[],[f120,f122])).

fof(f122,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f64,f95])).

fof(f120,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f118])).

fof(f129,plain,
    ( spl3_7
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f122,f93,f126])).

fof(f121,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f59,f118])).

fof(f59,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f52])).

fof(f116,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f62,f113])).

fof(f62,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f111,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f58,f108])).

fof(f58,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f52])).

fof(f106,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f57,f103])).

fof(f57,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f101,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f56,f98])).

fof(f56,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f52])).

fof(f96,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f55,f93])).

fof(f55,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f52])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.14  % Command    : run_vampire %s %d
% 0.13/0.35  % Computer   : n017.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % WCLimit    : 600
% 0.13/0.35  % DateTime   : Tue Dec  1 09:53:01 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.21/0.51  % (11277)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 0.21/0.51  % (11272)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.51  % (11268)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (11273)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.51  % (11269)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.52  % (11279)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  % (11273)Refutation not found, incomplete strategy% (11273)------------------------------
% 0.21/0.52  % (11273)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (11273)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.52  
% 0.21/0.52  % (11273)Memory used [KB]: 6268
% 0.21/0.52  % (11273)Time elapsed: 0.077 s
% 0.21/0.52  % (11273)------------------------------
% 0.21/0.52  % (11273)------------------------------
% 0.21/0.52  % (11293)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.52  % (11287)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (11276)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 0.21/0.53  % (11280)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.53  % (11289)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 0.21/0.53  % (11291)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.53  % (11288)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.53  % (11281)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.53  % (11270)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.53  % (11275)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.54  % (11274)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.54  % (11290)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.54  % (11284)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.54  % (11292)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.54  % (11270)Refutation found. Thanks to Tanya!
% 0.21/0.54  % SZS status Theorem for theBenchmark
% 0.21/0.55  % (11283)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 1.46/0.55  % (11285)lrs+1002_1_add=large:afr=on:afp=1000:afq=1.1:amm=sco:anc=none:er=known:fsr=off:gs=on:gsem=off:lma=on:nm=2:newcnf=on:nwc=2:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sp=reverse_arity:updr=off_145 on theBenchmark
% 1.46/0.55  % (11274)Refutation not found, incomplete strategy% (11274)------------------------------
% 1.46/0.55  % (11274)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.55  % (11274)Termination reason: Refutation not found, incomplete strategy
% 1.46/0.55  
% 1.46/0.55  % (11274)Memory used [KB]: 10874
% 1.46/0.55  % (11274)Time elapsed: 0.136 s
% 1.46/0.55  % (11274)------------------------------
% 1.46/0.55  % (11274)------------------------------
% 1.46/0.56  % (11282)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 1.46/0.56  % (11281)Refutation not found, incomplete strategy% (11281)------------------------------
% 1.46/0.56  % (11281)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.56  % SZS output start Proof for theBenchmark
% 1.46/0.56  fof(f770,plain,(
% 1.46/0.56    $false),
% 1.46/0.56    inference(avatar_sat_refutation,[],[f96,f101,f106,f111,f116,f121,f129,f134,f139,f145,f152,f161,f166,f173,f190,f197,f218,f229,f239,f252,f257,f262,f267,f290,f296,f302,f336,f345,f350,f370,f379,f392,f422,f427,f437,f468,f478,f483,f490,f504,f512,f518,f570,f576,f621,f665,f744,f766,f769])).
% 1.46/0.56  fof(f769,plain,(
% 1.46/0.56    k2_struct_0(sK0) != k1_relat_1(sK2) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_funct_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | sK2 != k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)),
% 1.46/0.56    introduced(theory_tautology_sat_conflict,[])).
% 1.46/0.56  fof(f766,plain,(
% 1.46/0.56    ~spl3_3 | ~spl3_23 | ~spl3_28 | ~spl3_44 | ~spl3_46 | ~spl3_52 | ~spl3_62 | spl3_69 | ~spl3_79),
% 1.46/0.56    inference(avatar_contradiction_clause,[],[f765])).
% 1.46/0.56  fof(f765,plain,(
% 1.46/0.56    $false | (~spl3_3 | ~spl3_23 | ~spl3_28 | ~spl3_44 | ~spl3_46 | ~spl3_52 | ~spl3_62 | spl3_69 | ~spl3_79)),
% 1.46/0.56    inference(subsumption_resolution,[],[f764,f238])).
% 1.46/0.56  fof(f238,plain,(
% 1.46/0.56    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_23),
% 1.46/0.56    inference(avatar_component_clause,[],[f236])).
% 1.46/0.56  fof(f236,plain,(
% 1.46/0.56    spl3_23 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 1.46/0.56  fof(f764,plain,(
% 1.46/0.56    k2_struct_0(sK1) != k2_relat_1(sK2) | (~spl3_3 | ~spl3_28 | ~spl3_44 | ~spl3_46 | ~spl3_52 | ~spl3_62 | spl3_69 | ~spl3_79)),
% 1.46/0.56    inference(forward_demodulation,[],[f763,f482])).
% 1.46/0.56  fof(f482,plain,(
% 1.46/0.56    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_52),
% 1.46/0.56    inference(avatar_component_clause,[],[f480])).
% 1.46/0.56  fof(f480,plain,(
% 1.46/0.56    spl3_52 <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 1.46/0.56  fof(f763,plain,(
% 1.46/0.56    k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_3 | ~spl3_28 | ~spl3_44 | ~spl3_46 | ~spl3_62 | spl3_69 | ~spl3_79)),
% 1.46/0.56    inference(subsumption_resolution,[],[f762,f660])).
% 1.46/0.56  fof(f660,plain,(
% 1.46/0.56    ~v2_funct_1(k2_funct_1(sK2)) | spl3_69),
% 1.46/0.56    inference(avatar_component_clause,[],[f658])).
% 1.46/0.56  fof(f658,plain,(
% 1.46/0.56    spl3_69 <=> v2_funct_1(k2_funct_1(sK2))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_69])])).
% 1.46/0.56  fof(f762,plain,(
% 1.46/0.56    v2_funct_1(k2_funct_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_3 | ~spl3_28 | ~spl3_44 | ~spl3_46 | ~spl3_62 | ~spl3_79)),
% 1.46/0.56    inference(forward_demodulation,[],[f761,f575])).
% 1.46/0.56  fof(f575,plain,(
% 1.46/0.56    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_62),
% 1.46/0.56    inference(avatar_component_clause,[],[f573])).
% 1.46/0.56  fof(f573,plain,(
% 1.46/0.56    spl3_62 <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 1.46/0.56  fof(f761,plain,(
% 1.46/0.56    v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_3 | ~spl3_28 | ~spl3_44 | ~spl3_46 | ~spl3_79)),
% 1.46/0.56    inference(subsumption_resolution,[],[f760,f105])).
% 1.46/0.56  fof(f105,plain,(
% 1.46/0.56    l1_struct_0(sK1) | ~spl3_3),
% 1.46/0.56    inference(avatar_component_clause,[],[f103])).
% 1.46/0.56  fof(f103,plain,(
% 1.46/0.56    spl3_3 <=> l1_struct_0(sK1)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.46/0.56  fof(f760,plain,(
% 1.46/0.56    v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~l1_struct_0(sK1) | (~spl3_28 | ~spl3_44 | ~spl3_46 | ~spl3_79)),
% 1.46/0.56    inference(subsumption_resolution,[],[f759,f436])).
% 1.46/0.56  fof(f436,plain,(
% 1.46/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_46),
% 1.46/0.56    inference(avatar_component_clause,[],[f434])).
% 1.46/0.56  fof(f434,plain,(
% 1.46/0.56    spl3_46 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 1.46/0.56  fof(f759,plain,(
% 1.46/0.56    v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~l1_struct_0(sK1) | (~spl3_28 | ~spl3_44 | ~spl3_79)),
% 1.46/0.56    inference(subsumption_resolution,[],[f757,f426])).
% 1.46/0.56  fof(f426,plain,(
% 1.46/0.56    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_44),
% 1.46/0.56    inference(avatar_component_clause,[],[f424])).
% 1.46/0.56  fof(f424,plain,(
% 1.46/0.56    spl3_44 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 1.46/0.56  fof(f757,plain,(
% 1.46/0.56    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~l1_struct_0(sK1) | (~spl3_28 | ~spl3_79)),
% 1.46/0.56    inference(superposition,[],[f743,f266])).
% 1.46/0.56  fof(f266,plain,(
% 1.46/0.56    u1_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_28),
% 1.46/0.56    inference(avatar_component_clause,[],[f264])).
% 1.46/0.56  fof(f264,plain,(
% 1.46/0.56    spl3_28 <=> u1_struct_0(sK1) = k2_relat_1(sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 1.46/0.56  fof(f743,plain,(
% 1.46/0.56    ( ! [X0] : (~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X0)) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X0),sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0)))) | k2_struct_0(X0) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(X0),sK2) | ~l1_struct_0(X0)) ) | ~spl3_79),
% 1.46/0.56    inference(avatar_component_clause,[],[f742])).
% 1.46/0.56  fof(f742,plain,(
% 1.46/0.56    spl3_79 <=> ! [X0] : (v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X0),sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0)))) | k2_struct_0(X0) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(X0),sK2) | ~l1_struct_0(X0))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_79])])).
% 1.46/0.56  fof(f744,plain,(
% 1.46/0.56    spl3_79 | ~spl3_1 | ~spl3_49 | ~spl3_65),
% 1.46/0.56    inference(avatar_split_clause,[],[f630,f619,f465,f93,f742])).
% 1.46/0.56  fof(f93,plain,(
% 1.46/0.56    spl3_1 <=> l1_struct_0(sK0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.46/0.56  fof(f465,plain,(
% 1.46/0.56    spl3_49 <=> u1_struct_0(sK0) = k1_relat_1(sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 1.46/0.56  fof(f619,plain,(
% 1.46/0.56    spl3_65 <=> ! [X1,X0] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 1.46/0.56  fof(f630,plain,(
% 1.46/0.56    ( ! [X0] : (v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X0),sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0)))) | k2_struct_0(X0) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(X0),sK2) | ~l1_struct_0(X0)) ) | (~spl3_1 | ~spl3_49 | ~spl3_65)),
% 1.46/0.56    inference(forward_demodulation,[],[f629,f467])).
% 1.46/0.56  fof(f467,plain,(
% 1.46/0.56    u1_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_49),
% 1.46/0.56    inference(avatar_component_clause,[],[f465])).
% 1.46/0.56  fof(f629,plain,(
% 1.46/0.56    ( ! [X0] : (~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0)))) | k2_struct_0(X0) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(X0),sK2) | ~l1_struct_0(X0) | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2))) ) | (~spl3_1 | ~spl3_49 | ~spl3_65)),
% 1.46/0.56    inference(forward_demodulation,[],[f628,f467])).
% 1.46/0.56  fof(f628,plain,(
% 1.46/0.56    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X0)))) | k2_struct_0(X0) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(X0),sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2))) ) | (~spl3_1 | ~spl3_49 | ~spl3_65)),
% 1.46/0.56    inference(forward_demodulation,[],[f627,f467])).
% 1.46/0.56  fof(f627,plain,(
% 1.46/0.56    ( ! [X0] : (k2_struct_0(X0) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(X0),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2))) ) | (~spl3_1 | ~spl3_49 | ~spl3_65)),
% 1.46/0.56    inference(forward_demodulation,[],[f625,f467])).
% 1.46/0.56  fof(f625,plain,(
% 1.46/0.56    ( ! [X0] : (k2_struct_0(X0) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X0),sK2))) ) | (~spl3_1 | ~spl3_65)),
% 1.46/0.56    inference(resolution,[],[f620,f95])).
% 1.46/0.56  fof(f95,plain,(
% 1.46/0.56    l1_struct_0(sK0) | ~spl3_1),
% 1.46/0.56    inference(avatar_component_clause,[],[f93])).
% 1.46/0.56  fof(f620,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~l1_struct_0(X0) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2))) ) | ~spl3_65),
% 1.46/0.56    inference(avatar_component_clause,[],[f619])).
% 1.46/0.56  fof(f665,plain,(
% 1.46/0.56    ~spl3_69 | spl3_70 | ~spl3_17 | ~spl3_33 | ~spl3_56 | ~spl3_57 | ~spl3_61),
% 1.46/0.56    inference(avatar_split_clause,[],[f594,f567,f509,f501,f333,f194,f662,f658])).
% 1.46/0.56  fof(f662,plain,(
% 1.46/0.56    spl3_70 <=> sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_70])])).
% 1.46/0.56  fof(f194,plain,(
% 1.46/0.56    spl3_17 <=> sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.46/0.56  fof(f333,plain,(
% 1.46/0.56    spl3_33 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 1.46/0.56  fof(f501,plain,(
% 1.46/0.56    spl3_56 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 1.46/0.56  fof(f509,plain,(
% 1.46/0.56    spl3_57 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_57])])).
% 1.46/0.56  fof(f567,plain,(
% 1.46/0.56    spl3_61 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 1.46/0.56  fof(f594,plain,(
% 1.46/0.56    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | (~spl3_17 | ~spl3_33 | ~spl3_56 | ~spl3_57 | ~spl3_61)),
% 1.46/0.56    inference(forward_demodulation,[],[f593,f196])).
% 1.46/0.56  fof(f196,plain,(
% 1.46/0.56    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl3_17),
% 1.46/0.56    inference(avatar_component_clause,[],[f194])).
% 1.46/0.56  fof(f593,plain,(
% 1.46/0.56    ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_33 | ~spl3_56 | ~spl3_57 | ~spl3_61)),
% 1.46/0.56    inference(subsumption_resolution,[],[f592,f335])).
% 1.46/0.56  fof(f335,plain,(
% 1.46/0.56    v1_funct_1(k2_funct_1(sK2)) | ~spl3_33),
% 1.46/0.56    inference(avatar_component_clause,[],[f333])).
% 1.46/0.56  fof(f592,plain,(
% 1.46/0.56    ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_56 | ~spl3_57 | ~spl3_61)),
% 1.46/0.56    inference(subsumption_resolution,[],[f591,f511])).
% 1.46/0.56  fof(f511,plain,(
% 1.46/0.56    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~spl3_57),
% 1.46/0.56    inference(avatar_component_clause,[],[f509])).
% 1.46/0.56  fof(f591,plain,(
% 1.46/0.56    ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_56 | ~spl3_61)),
% 1.46/0.56    inference(subsumption_resolution,[],[f590,f503])).
% 1.46/0.56  fof(f503,plain,(
% 1.46/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_56),
% 1.46/0.56    inference(avatar_component_clause,[],[f501])).
% 1.46/0.56  fof(f590,plain,(
% 1.46/0.56    ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~spl3_61),
% 1.46/0.56    inference(trivial_inequality_removal,[],[f583])).
% 1.46/0.56  fof(f583,plain,(
% 1.46/0.56    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v2_funct_1(k2_funct_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~spl3_61),
% 1.46/0.56    inference(superposition,[],[f86,f569])).
% 1.46/0.56  fof(f569,plain,(
% 1.46/0.56    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_61),
% 1.46/0.56    inference(avatar_component_clause,[],[f567])).
% 1.46/0.56  fof(f86,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f46])).
% 1.46/0.56  fof(f46,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.46/0.56    inference(flattening,[],[f45])).
% 1.46/0.56  fof(f45,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.46/0.56    inference(ennf_transformation,[],[f17])).
% 1.46/0.56  fof(f17,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 1.46/0.56  fof(f621,plain,(
% 1.46/0.56    spl3_65 | ~spl3_4 | ~spl3_5),
% 1.46/0.56    inference(avatar_split_clause,[],[f331,f113,f108,f619])).
% 1.46/0.56  fof(f108,plain,(
% 1.46/0.56    spl3_4 <=> v1_funct_1(sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.46/0.56  fof(f113,plain,(
% 1.46/0.56    spl3_5 <=> v2_funct_1(sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.46/0.56  fof(f331,plain,(
% 1.46/0.56    ( ! [X0,X1] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) ) | (~spl3_4 | ~spl3_5)),
% 1.46/0.56    inference(subsumption_resolution,[],[f330,f110])).
% 1.46/0.56  fof(f110,plain,(
% 1.46/0.56    v1_funct_1(sK2) | ~spl3_4),
% 1.46/0.56    inference(avatar_component_clause,[],[f108])).
% 1.46/0.56  fof(f330,plain,(
% 1.46/0.56    ( ! [X0,X1] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(sK2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) ) | ~spl3_5),
% 1.46/0.56    inference(resolution,[],[f65,f115])).
% 1.46/0.56  fof(f115,plain,(
% 1.46/0.56    v2_funct_1(sK2) | ~spl3_5),
% 1.46/0.56    inference(avatar_component_clause,[],[f113])).
% 1.46/0.56  fof(f65,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f25])).
% 1.46/0.56  fof(f25,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.46/0.56    inference(flattening,[],[f24])).
% 1.46/0.56  fof(f24,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.46/0.56    inference(ennf_transformation,[],[f18])).
% 1.46/0.56  fof(f18,axiom,(
% 1.46/0.56    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).
% 1.46/0.56  fof(f576,plain,(
% 1.46/0.56    spl3_62 | ~spl3_4 | ~spl3_5 | ~spl3_44 | ~spl3_46 | ~spl3_52),
% 1.46/0.56    inference(avatar_split_clause,[],[f531,f480,f434,f424,f113,f108,f573])).
% 1.46/0.56  fof(f531,plain,(
% 1.46/0.56    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_4 | ~spl3_5 | ~spl3_44 | ~spl3_46 | ~spl3_52)),
% 1.46/0.56    inference(subsumption_resolution,[],[f530,f110])).
% 1.46/0.56  fof(f530,plain,(
% 1.46/0.56    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_1(sK2) | (~spl3_5 | ~spl3_44 | ~spl3_46 | ~spl3_52)),
% 1.46/0.56    inference(subsumption_resolution,[],[f529,f426])).
% 1.46/0.56  fof(f529,plain,(
% 1.46/0.56    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_5 | ~spl3_46 | ~spl3_52)),
% 1.46/0.56    inference(subsumption_resolution,[],[f528,f436])).
% 1.46/0.56  fof(f528,plain,(
% 1.46/0.56    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_5 | ~spl3_52)),
% 1.46/0.56    inference(subsumption_resolution,[],[f527,f115])).
% 1.46/0.56  fof(f527,plain,(
% 1.46/0.56    ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~spl3_52),
% 1.46/0.56    inference(trivial_inequality_removal,[],[f520])).
% 1.46/0.56  fof(f520,plain,(
% 1.46/0.56    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~spl3_52),
% 1.46/0.56    inference(superposition,[],[f86,f482])).
% 1.46/0.56  fof(f570,plain,(
% 1.46/0.56    spl3_61 | ~spl3_27 | ~spl3_43 | ~spl3_51 | ~spl3_53),
% 1.46/0.56    inference(avatar_split_clause,[],[f564,f487,f475,f419,f259,f567])).
% 1.46/0.56  fof(f259,plain,(
% 1.46/0.56    spl3_27 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 1.46/0.56  fof(f419,plain,(
% 1.46/0.56    spl3_43 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 1.46/0.56  fof(f475,plain,(
% 1.46/0.56    spl3_51 <=> k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 1.46/0.56  fof(f487,plain,(
% 1.46/0.56    spl3_53 <=> k2_funct_1(sK2) = k3_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 1.46/0.56  fof(f564,plain,(
% 1.46/0.56    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_27 | ~spl3_43 | ~spl3_51 | ~spl3_53)),
% 1.46/0.56    inference(forward_demodulation,[],[f563,f477])).
% 1.46/0.56  fof(f477,plain,(
% 1.46/0.56    k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_51),
% 1.46/0.56    inference(avatar_component_clause,[],[f475])).
% 1.46/0.56  fof(f563,plain,(
% 1.46/0.56    k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_27 | ~spl3_43 | ~spl3_53)),
% 1.46/0.56    inference(forward_demodulation,[],[f562,f489])).
% 1.46/0.56  fof(f489,plain,(
% 1.46/0.56    k2_funct_1(sK2) = k3_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_53),
% 1.46/0.56    inference(avatar_component_clause,[],[f487])).
% 1.46/0.56  fof(f562,plain,(
% 1.46/0.56    k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k3_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | (~spl3_27 | ~spl3_43)),
% 1.46/0.56    inference(forward_demodulation,[],[f297,f421])).
% 1.46/0.56  fof(f421,plain,(
% 1.46/0.56    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_43),
% 1.46/0.56    inference(avatar_component_clause,[],[f419])).
% 1.46/0.56  fof(f297,plain,(
% 1.46/0.56    k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) = k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | ~spl3_27),
% 1.46/0.56    inference(resolution,[],[f82,f261])).
% 1.46/0.56  fof(f261,plain,(
% 1.46/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_27),
% 1.46/0.56    inference(avatar_component_clause,[],[f259])).
% 1.46/0.56  fof(f82,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2))) )),
% 1.46/0.56    inference(cnf_transformation,[],[f42])).
% 1.46/0.56  fof(f42,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(ennf_transformation,[],[f10])).
% 1.46/0.56  fof(f10,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k1_relset_1(X0,X1,X2) = k2_relset_1(X1,X0,k3_relset_1(X0,X1,X2)) & k2_relset_1(X0,X1,X2) = k1_relset_1(X1,X0,k3_relset_1(X0,X1,X2))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_relset_1)).
% 1.46/0.56  fof(f518,plain,(
% 1.46/0.56    spl3_58 | ~spl3_39 | ~spl3_44 | ~spl3_46),
% 1.46/0.56    inference(avatar_split_clause,[],[f454,f434,f424,f377,f515])).
% 1.46/0.56  fof(f515,plain,(
% 1.46/0.56    spl3_58 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_58])])).
% 1.46/0.56  fof(f377,plain,(
% 1.46/0.56    spl3_39 <=> ! [X1,X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | r2_funct_2(X0,X1,sK2,sK2))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 1.46/0.56  fof(f454,plain,(
% 1.46/0.56    r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | (~spl3_39 | ~spl3_44 | ~spl3_46)),
% 1.46/0.56    inference(subsumption_resolution,[],[f443,f426])).
% 1.46/0.56  fof(f443,plain,(
% 1.46/0.56    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | (~spl3_39 | ~spl3_46)),
% 1.46/0.56    inference(resolution,[],[f436,f378])).
% 1.46/0.56  fof(f378,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | r2_funct_2(X0,X1,sK2,sK2)) ) | ~spl3_39),
% 1.46/0.56    inference(avatar_component_clause,[],[f377])).
% 1.46/0.56  fof(f512,plain,(
% 1.46/0.56    spl3_57 | ~spl3_13 | ~spl3_14 | ~spl3_34 | ~spl3_41),
% 1.46/0.56    inference(avatar_split_clause,[],[f413,f389,f342,f170,f163,f509])).
% 1.46/0.56  fof(f163,plain,(
% 1.46/0.56    spl3_13 <=> v1_relat_1(sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.46/0.56  fof(f170,plain,(
% 1.46/0.56    spl3_14 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.46/0.56  fof(f342,plain,(
% 1.46/0.56    spl3_34 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 1.46/0.56  fof(f389,plain,(
% 1.46/0.56    spl3_41 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 1.46/0.56  fof(f413,plain,(
% 1.46/0.56    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | (~spl3_13 | ~spl3_14 | ~spl3_34 | ~spl3_41)),
% 1.46/0.56    inference(backward_demodulation,[],[f344,f397])).
% 1.46/0.56  fof(f397,plain,(
% 1.46/0.56    k2_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_13 | ~spl3_14 | ~spl3_41)),
% 1.46/0.56    inference(subsumption_resolution,[],[f396,f165])).
% 1.46/0.56  fof(f165,plain,(
% 1.46/0.56    v1_relat_1(sK2) | ~spl3_13),
% 1.46/0.56    inference(avatar_component_clause,[],[f163])).
% 1.46/0.56  fof(f396,plain,(
% 1.46/0.56    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl3_14 | ~spl3_41)),
% 1.46/0.56    inference(subsumption_resolution,[],[f395,f172])).
% 1.46/0.56  fof(f172,plain,(
% 1.46/0.56    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_14),
% 1.46/0.56    inference(avatar_component_clause,[],[f170])).
% 1.46/0.56  fof(f395,plain,(
% 1.46/0.56    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v4_relat_1(sK2,k2_struct_0(sK0)) | ~v1_relat_1(sK2) | ~spl3_41),
% 1.46/0.56    inference(resolution,[],[f391,f73])).
% 1.46/0.56  fof(f73,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f53])).
% 1.46/0.56  fof(f53,plain,(
% 1.46/0.56    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.46/0.56    inference(nnf_transformation,[],[f36])).
% 1.46/0.56  fof(f36,plain,(
% 1.46/0.56    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.46/0.56    inference(flattening,[],[f35])).
% 1.46/0.56  fof(f35,plain,(
% 1.46/0.56    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.46/0.56    inference(ennf_transformation,[],[f12])).
% 1.46/0.56  fof(f12,axiom,(
% 1.46/0.56    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 1.46/0.56  fof(f391,plain,(
% 1.46/0.56    v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_41),
% 1.46/0.56    inference(avatar_component_clause,[],[f389])).
% 1.46/0.56  fof(f344,plain,(
% 1.46/0.56    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~spl3_34),
% 1.46/0.56    inference(avatar_component_clause,[],[f342])).
% 1.46/0.56  fof(f504,plain,(
% 1.46/0.56    spl3_56 | ~spl3_13 | ~spl3_14 | ~spl3_35 | ~spl3_41),
% 1.46/0.56    inference(avatar_split_clause,[],[f414,f389,f347,f170,f163,f501])).
% 1.46/0.56  fof(f347,plain,(
% 1.46/0.56    spl3_35 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 1.46/0.56  fof(f414,plain,(
% 1.46/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_13 | ~spl3_14 | ~spl3_35 | ~spl3_41)),
% 1.46/0.56    inference(backward_demodulation,[],[f349,f397])).
% 1.46/0.56  fof(f349,plain,(
% 1.46/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~spl3_35),
% 1.46/0.56    inference(avatar_component_clause,[],[f347])).
% 1.46/0.56  fof(f490,plain,(
% 1.46/0.56    spl3_53 | ~spl3_13 | ~spl3_14 | ~spl3_32 | ~spl3_41),
% 1.46/0.56    inference(avatar_split_clause,[],[f412,f389,f299,f170,f163,f487])).
% 1.46/0.56  fof(f299,plain,(
% 1.46/0.56    spl3_32 <=> k2_funct_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 1.46/0.56  fof(f412,plain,(
% 1.46/0.56    k2_funct_1(sK2) = k3_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_13 | ~spl3_14 | ~spl3_32 | ~spl3_41)),
% 1.46/0.56    inference(backward_demodulation,[],[f301,f397])).
% 1.46/0.56  fof(f301,plain,(
% 1.46/0.56    k2_funct_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_32),
% 1.46/0.56    inference(avatar_component_clause,[],[f299])).
% 1.46/0.56  fof(f483,plain,(
% 1.46/0.56    spl3_52 | ~spl3_13 | ~spl3_14 | ~spl3_31 | ~spl3_41),
% 1.46/0.56    inference(avatar_split_clause,[],[f411,f389,f293,f170,f163,f480])).
% 1.46/0.56  fof(f293,plain,(
% 1.46/0.56    spl3_31 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 1.46/0.56  fof(f411,plain,(
% 1.46/0.56    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_13 | ~spl3_14 | ~spl3_31 | ~spl3_41)),
% 1.46/0.56    inference(backward_demodulation,[],[f295,f397])).
% 1.46/0.56  fof(f295,plain,(
% 1.46/0.56    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_31),
% 1.46/0.56    inference(avatar_component_clause,[],[f293])).
% 1.46/0.56  fof(f478,plain,(
% 1.46/0.56    spl3_51 | ~spl3_13 | ~spl3_14 | ~spl3_30 | ~spl3_41),
% 1.46/0.56    inference(avatar_split_clause,[],[f410,f389,f287,f170,f163,f475])).
% 1.46/0.56  fof(f287,plain,(
% 1.46/0.56    spl3_30 <=> k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 1.46/0.56  fof(f410,plain,(
% 1.46/0.56    k1_relat_1(sK2) = k1_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_13 | ~spl3_14 | ~spl3_30 | ~spl3_41)),
% 1.46/0.56    inference(backward_demodulation,[],[f289,f397])).
% 1.46/0.56  fof(f289,plain,(
% 1.46/0.56    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_30),
% 1.46/0.56    inference(avatar_component_clause,[],[f287])).
% 1.46/0.56  fof(f468,plain,(
% 1.46/0.56    spl3_49 | ~spl3_7 | ~spl3_13 | ~spl3_14 | ~spl3_41),
% 1.46/0.56    inference(avatar_split_clause,[],[f405,f389,f170,f163,f126,f465])).
% 1.46/0.56  fof(f126,plain,(
% 1.46/0.56    spl3_7 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.46/0.56  fof(f405,plain,(
% 1.46/0.56    u1_struct_0(sK0) = k1_relat_1(sK2) | (~spl3_7 | ~spl3_13 | ~spl3_14 | ~spl3_41)),
% 1.46/0.56    inference(backward_demodulation,[],[f128,f397])).
% 1.46/0.56  fof(f128,plain,(
% 1.46/0.56    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_7),
% 1.46/0.56    inference(avatar_component_clause,[],[f126])).
% 1.46/0.56  fof(f437,plain,(
% 1.46/0.56    spl3_46 | ~spl3_13 | ~spl3_14 | ~spl3_27 | ~spl3_41),
% 1.46/0.56    inference(avatar_split_clause,[],[f408,f389,f259,f170,f163,f434])).
% 1.46/0.56  fof(f408,plain,(
% 1.46/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_13 | ~spl3_14 | ~spl3_27 | ~spl3_41)),
% 1.46/0.56    inference(backward_demodulation,[],[f261,f397])).
% 1.46/0.56  fof(f427,plain,(
% 1.46/0.56    spl3_44 | ~spl3_13 | ~spl3_14 | ~spl3_26 | ~spl3_41),
% 1.46/0.56    inference(avatar_split_clause,[],[f407,f389,f254,f170,f163,f424])).
% 1.46/0.56  fof(f254,plain,(
% 1.46/0.56    spl3_26 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 1.46/0.56  fof(f407,plain,(
% 1.46/0.56    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_13 | ~spl3_14 | ~spl3_26 | ~spl3_41)),
% 1.46/0.56    inference(backward_demodulation,[],[f256,f397])).
% 1.46/0.56  fof(f256,plain,(
% 1.46/0.56    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_26),
% 1.46/0.56    inference(avatar_component_clause,[],[f254])).
% 1.46/0.56  fof(f422,plain,(
% 1.46/0.56    spl3_43 | ~spl3_13 | ~spl3_14 | ~spl3_41),
% 1.46/0.56    inference(avatar_split_clause,[],[f397,f389,f170,f163,f419])).
% 1.46/0.56  fof(f392,plain,(
% 1.46/0.56    spl3_41 | spl3_25 | ~spl3_26 | ~spl3_27 | ~spl3_37),
% 1.46/0.56    inference(avatar_split_clause,[],[f387,f368,f259,f254,f249,f389])).
% 1.46/0.56  fof(f249,plain,(
% 1.46/0.56    spl3_25 <=> v1_xboole_0(k2_relat_1(sK2))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 1.46/0.56  fof(f368,plain,(
% 1.46/0.56    spl3_37 <=> ! [X1,X0] : (~v1_funct_2(sK2,X0,X1) | v1_partfun1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 1.46/0.56  fof(f387,plain,(
% 1.46/0.56    v1_partfun1(sK2,k2_struct_0(sK0)) | (spl3_25 | ~spl3_26 | ~spl3_27 | ~spl3_37)),
% 1.46/0.56    inference(subsumption_resolution,[],[f386,f251])).
% 1.46/0.56  fof(f251,plain,(
% 1.46/0.56    ~v1_xboole_0(k2_relat_1(sK2)) | spl3_25),
% 1.46/0.56    inference(avatar_component_clause,[],[f249])).
% 1.46/0.56  fof(f386,plain,(
% 1.46/0.56    v1_partfun1(sK2,k2_struct_0(sK0)) | v1_xboole_0(k2_relat_1(sK2)) | (~spl3_26 | ~spl3_27 | ~spl3_37)),
% 1.46/0.56    inference(subsumption_resolution,[],[f385,f256])).
% 1.46/0.56  fof(f385,plain,(
% 1.46/0.56    v1_partfun1(sK2,k2_struct_0(sK0)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | v1_xboole_0(k2_relat_1(sK2)) | (~spl3_27 | ~spl3_37)),
% 1.46/0.56    inference(resolution,[],[f369,f261])).
% 1.46/0.56  fof(f369,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(sK2,X0) | ~v1_funct_2(sK2,X0,X1) | v1_xboole_0(X1)) ) | ~spl3_37),
% 1.46/0.56    inference(avatar_component_clause,[],[f368])).
% 1.46/0.56  fof(f379,plain,(
% 1.46/0.56    spl3_39 | ~spl3_4),
% 1.46/0.56    inference(avatar_split_clause,[],[f285,f108,f377])).
% 1.46/0.56  fof(f285,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | r2_funct_2(X0,X1,sK2,sK2)) ) | ~spl3_4),
% 1.46/0.56    inference(resolution,[],[f91,f110])).
% 1.46/0.56  fof(f91,plain,(
% 1.46/0.56    ( ! [X0,X3,X1] : (~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | r2_funct_2(X0,X1,X3,X3)) )),
% 1.46/0.56    inference(duplicate_literal_removal,[],[f90])).
% 1.46/0.56  fof(f90,plain,(
% 1.46/0.56    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 1.46/0.56    inference(equality_resolution,[],[f88])).
% 1.46/0.56  fof(f88,plain,(
% 1.46/0.56    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f54])).
% 1.46/0.56  fof(f54,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.46/0.56    inference(nnf_transformation,[],[f48])).
% 1.46/0.56  fof(f48,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.46/0.56    inference(flattening,[],[f47])).
% 1.46/0.56  fof(f47,plain,(
% 1.46/0.56    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.46/0.56    inference(ennf_transformation,[],[f13])).
% 1.46/0.56  fof(f13,axiom,(
% 1.46/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 1.46/0.56  fof(f370,plain,(
% 1.46/0.56    spl3_37 | ~spl3_4),
% 1.46/0.56    inference(avatar_split_clause,[],[f283,f108,f368])).
% 1.46/0.56  fof(f283,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~v1_funct_2(sK2,X0,X1) | v1_partfun1(sK2,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) ) | ~spl3_4),
% 1.46/0.56    inference(resolution,[],[f72,f110])).
% 1.46/0.56  fof(f72,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v1_funct_2(X2,X0,X1) | v1_partfun1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f34])).
% 1.46/0.56  fof(f34,plain,(
% 1.46/0.56    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.46/0.56    inference(flattening,[],[f33])).
% 1.46/0.56  fof(f33,plain,(
% 1.46/0.56    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 1.46/0.56    inference(ennf_transformation,[],[f11])).
% 1.46/0.56  fof(f11,axiom,(
% 1.46/0.56    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 1.46/0.56  fof(f350,plain,(
% 1.46/0.56    spl3_35 | ~spl3_11 | ~spl3_23 | ~spl3_32),
% 1.46/0.56    inference(avatar_split_clause,[],[f340,f299,f236,f149,f347])).
% 1.46/0.56  fof(f149,plain,(
% 1.46/0.56    spl3_11 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 1.46/0.56  fof(f340,plain,(
% 1.46/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | (~spl3_11 | ~spl3_23 | ~spl3_32)),
% 1.46/0.56    inference(forward_demodulation,[],[f339,f301])).
% 1.46/0.56  fof(f339,plain,(
% 1.46/0.56    m1_subset_1(k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | (~spl3_11 | ~spl3_23)),
% 1.46/0.56    inference(forward_demodulation,[],[f206,f238])).
% 1.46/0.56  fof(f206,plain,(
% 1.46/0.56    m1_subset_1(k3_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | ~spl3_11),
% 1.46/0.56    inference(resolution,[],[f78,f151])).
% 1.46/0.56  fof(f151,plain,(
% 1.46/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_11),
% 1.46/0.56    inference(avatar_component_clause,[],[f149])).
% 1.46/0.56  fof(f78,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 1.46/0.56    inference(cnf_transformation,[],[f40])).
% 1.46/0.56  fof(f40,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(ennf_transformation,[],[f6])).
% 1.46/0.56  fof(f6,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => m1_subset_1(k3_relset_1(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k3_relset_1)).
% 1.46/0.56  fof(f345,plain,(
% 1.46/0.56    spl3_34 | ~spl3_4 | ~spl3_5 | ~spl3_26 | ~spl3_27 | ~spl3_31),
% 1.46/0.56    inference(avatar_split_clause,[],[f325,f293,f259,f254,f113,f108,f342])).
% 1.46/0.56  fof(f325,plain,(
% 1.46/0.56    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | (~spl3_4 | ~spl3_5 | ~spl3_26 | ~spl3_27 | ~spl3_31)),
% 1.46/0.56    inference(subsumption_resolution,[],[f324,f110])).
% 1.46/0.56  fof(f324,plain,(
% 1.46/0.56    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~v1_funct_1(sK2) | (~spl3_5 | ~spl3_26 | ~spl3_27 | ~spl3_31)),
% 1.46/0.56    inference(subsumption_resolution,[],[f323,f256])).
% 1.46/0.56  fof(f323,plain,(
% 1.46/0.56    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_5 | ~spl3_27 | ~spl3_31)),
% 1.46/0.56    inference(subsumption_resolution,[],[f322,f261])).
% 1.46/0.56  fof(f322,plain,(
% 1.46/0.56    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_5 | ~spl3_31)),
% 1.46/0.56    inference(subsumption_resolution,[],[f311,f115])).
% 1.46/0.56  fof(f311,plain,(
% 1.46/0.56    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~spl3_31),
% 1.46/0.56    inference(trivial_inequality_removal,[],[f308])).
% 1.46/0.56  fof(f308,plain,(
% 1.46/0.56    k2_relat_1(sK2) != k2_relat_1(sK2) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~spl3_31),
% 1.46/0.56    inference(superposition,[],[f84,f295])).
% 1.46/0.56  fof(f84,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f44])).
% 1.46/0.56  fof(f44,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.46/0.56    inference(flattening,[],[f43])).
% 1.46/0.56  fof(f43,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.46/0.56    inference(ennf_transformation,[],[f14])).
% 1.46/0.56  fof(f14,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 1.46/0.56  fof(f336,plain,(
% 1.46/0.56    spl3_33 | ~spl3_4 | ~spl3_5 | ~spl3_26 | ~spl3_27 | ~spl3_31),
% 1.46/0.56    inference(avatar_split_clause,[],[f329,f293,f259,f254,f113,f108,f333])).
% 1.46/0.56  fof(f329,plain,(
% 1.46/0.56    v1_funct_1(k2_funct_1(sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_26 | ~spl3_27 | ~spl3_31)),
% 1.46/0.56    inference(subsumption_resolution,[],[f328,f110])).
% 1.46/0.56  fof(f328,plain,(
% 1.46/0.56    v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_5 | ~spl3_26 | ~spl3_27 | ~spl3_31)),
% 1.46/0.56    inference(subsumption_resolution,[],[f327,f256])).
% 1.46/0.56  fof(f327,plain,(
% 1.46/0.56    v1_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_5 | ~spl3_27 | ~spl3_31)),
% 1.46/0.56    inference(subsumption_resolution,[],[f326,f261])).
% 1.46/0.56  fof(f326,plain,(
% 1.46/0.56    v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_5 | ~spl3_31)),
% 1.46/0.56    inference(subsumption_resolution,[],[f310,f115])).
% 1.46/0.56  fof(f310,plain,(
% 1.46/0.56    v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~spl3_31),
% 1.46/0.56    inference(trivial_inequality_removal,[],[f309])).
% 1.46/0.56  fof(f309,plain,(
% 1.46/0.56    k2_relat_1(sK2) != k2_relat_1(sK2) | v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~spl3_31),
% 1.46/0.56    inference(superposition,[],[f83,f295])).
% 1.46/0.56  fof(f83,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2)) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f44])).
% 1.46/0.56  fof(f302,plain,(
% 1.46/0.56    spl3_32 | ~spl3_16 | ~spl3_27),
% 1.46/0.56    inference(avatar_split_clause,[],[f275,f259,f187,f299])).
% 1.46/0.56  fof(f187,plain,(
% 1.46/0.56    spl3_16 <=> k2_funct_1(sK2) = k4_relat_1(sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.46/0.56  fof(f275,plain,(
% 1.46/0.56    k2_funct_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_16 | ~spl3_27)),
% 1.46/0.56    inference(forward_demodulation,[],[f269,f189])).
% 1.46/0.56  fof(f189,plain,(
% 1.46/0.56    k2_funct_1(sK2) = k4_relat_1(sK2) | ~spl3_16),
% 1.46/0.56    inference(avatar_component_clause,[],[f187])).
% 1.46/0.56  fof(f269,plain,(
% 1.46/0.56    k4_relat_1(sK2) = k3_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_27),
% 1.46/0.56    inference(resolution,[],[f261,f76])).
% 1.46/0.56  fof(f76,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k3_relset_1(X0,X1,X2) = k4_relat_1(X2)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f38])).
% 1.46/0.56  fof(f38,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (k3_relset_1(X0,X1,X2) = k4_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(ennf_transformation,[],[f9])).
% 1.46/0.56  fof(f9,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k3_relset_1(X0,X1,X2) = k4_relat_1(X2))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k3_relset_1)).
% 1.46/0.56  fof(f296,plain,(
% 1.46/0.56    spl3_31 | ~spl3_27),
% 1.46/0.56    inference(avatar_split_clause,[],[f270,f259,f293])).
% 1.46/0.56  fof(f270,plain,(
% 1.46/0.56    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_27),
% 1.46/0.56    inference(resolution,[],[f261,f77])).
% 1.46/0.56  fof(f77,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f39])).
% 1.46/0.56  fof(f39,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(ennf_transformation,[],[f8])).
% 1.46/0.56  fof(f8,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.46/0.56  fof(f290,plain,(
% 1.46/0.56    spl3_30 | ~spl3_27),
% 1.46/0.56    inference(avatar_split_clause,[],[f268,f259,f287])).
% 1.46/0.56  fof(f268,plain,(
% 1.46/0.56    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_27),
% 1.46/0.56    inference(resolution,[],[f261,f75])).
% 1.46/0.56  fof(f75,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f37])).
% 1.46/0.56  fof(f37,plain,(
% 1.46/0.56    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(ennf_transformation,[],[f7])).
% 1.46/0.56  fof(f7,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 1.46/0.56  fof(f267,plain,(
% 1.46/0.56    spl3_28 | ~spl3_9 | ~spl3_11 | ~spl3_12),
% 1.46/0.56    inference(avatar_split_clause,[],[f234,f158,f149,f136,f264])).
% 1.46/0.56  fof(f136,plain,(
% 1.46/0.56    spl3_9 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.46/0.56  fof(f158,plain,(
% 1.46/0.56    spl3_12 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.46/0.56  fof(f234,plain,(
% 1.46/0.56    u1_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_9 | ~spl3_11 | ~spl3_12)),
% 1.46/0.56    inference(backward_demodulation,[],[f138,f224])).
% 1.46/0.56  fof(f224,plain,(
% 1.46/0.56    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_11 | ~spl3_12)),
% 1.46/0.56    inference(backward_demodulation,[],[f160,f201])).
% 1.46/0.56  fof(f201,plain,(
% 1.46/0.56    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_11),
% 1.46/0.56    inference(resolution,[],[f77,f151])).
% 1.46/0.56  fof(f160,plain,(
% 1.46/0.56    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_12),
% 1.46/0.56    inference(avatar_component_clause,[],[f158])).
% 1.46/0.56  fof(f138,plain,(
% 1.46/0.56    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_9),
% 1.46/0.56    inference(avatar_component_clause,[],[f136])).
% 1.46/0.56  fof(f262,plain,(
% 1.46/0.56    spl3_27 | ~spl3_11 | ~spl3_12),
% 1.46/0.56    inference(avatar_split_clause,[],[f232,f158,f149,f259])).
% 1.46/0.56  fof(f232,plain,(
% 1.46/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_11 | ~spl3_12)),
% 1.46/0.56    inference(backward_demodulation,[],[f151,f224])).
% 1.46/0.56  fof(f257,plain,(
% 1.46/0.56    spl3_26 | ~spl3_10 | ~spl3_11 | ~spl3_12),
% 1.46/0.56    inference(avatar_split_clause,[],[f233,f158,f149,f142,f254])).
% 1.46/0.56  fof(f142,plain,(
% 1.46/0.56    spl3_10 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 1.46/0.56  fof(f233,plain,(
% 1.46/0.56    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_10 | ~spl3_11 | ~spl3_12)),
% 1.46/0.56    inference(backward_demodulation,[],[f144,f224])).
% 1.46/0.56  fof(f144,plain,(
% 1.46/0.56    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_10),
% 1.46/0.56    inference(avatar_component_clause,[],[f142])).
% 1.46/0.56  fof(f252,plain,(
% 1.46/0.56    ~spl3_25 | spl3_2 | ~spl3_3 | ~spl3_23),
% 1.46/0.56    inference(avatar_split_clause,[],[f247,f236,f103,f98,f249])).
% 1.46/0.56  fof(f98,plain,(
% 1.46/0.56    spl3_2 <=> v2_struct_0(sK1)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.46/0.56  fof(f247,plain,(
% 1.46/0.56    ~v1_xboole_0(k2_relat_1(sK2)) | (spl3_2 | ~spl3_3 | ~spl3_23)),
% 1.46/0.56    inference(subsumption_resolution,[],[f246,f100])).
% 1.46/0.56  fof(f100,plain,(
% 1.46/0.56    ~v2_struct_0(sK1) | spl3_2),
% 1.46/0.56    inference(avatar_component_clause,[],[f98])).
% 1.46/0.56  fof(f246,plain,(
% 1.46/0.56    ~v1_xboole_0(k2_relat_1(sK2)) | v2_struct_0(sK1) | (~spl3_3 | ~spl3_23)),
% 1.46/0.56    inference(subsumption_resolution,[],[f245,f105])).
% 1.46/0.56  fof(f245,plain,(
% 1.46/0.56    ~v1_xboole_0(k2_relat_1(sK2)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_23),
% 1.46/0.56    inference(superposition,[],[f67,f238])).
% 1.46/0.56  fof(f67,plain,(
% 1.46/0.56    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f28])).
% 1.46/0.56  fof(f28,plain,(
% 1.46/0.56    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.46/0.56    inference(flattening,[],[f27])).
% 1.46/0.56  fof(f27,plain,(
% 1.46/0.56    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f16])).
% 1.46/0.56  fof(f16,axiom,(
% 1.46/0.56    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 1.46/0.56  fof(f239,plain,(
% 1.46/0.56    spl3_23 | ~spl3_11 | ~spl3_12),
% 1.46/0.56    inference(avatar_split_clause,[],[f224,f158,f149,f236])).
% 1.46/0.56  fof(f229,plain,(
% 1.46/0.56    spl3_22 | ~spl3_11),
% 1.46/0.56    inference(avatar_split_clause,[],[f201,f149,f226])).
% 1.46/0.56  fof(f226,plain,(
% 1.46/0.56    spl3_22 <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 1.46/0.56  fof(f218,plain,(
% 1.46/0.56    ~spl3_20 | ~spl3_7 | ~spl3_9),
% 1.46/0.56    inference(avatar_split_clause,[],[f208,f136,f126,f215])).
% 1.46/0.56  fof(f215,plain,(
% 1.46/0.56    spl3_20 <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 1.46/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.46/0.56  fof(f208,plain,(
% 1.46/0.56    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | (~spl3_7 | ~spl3_9)),
% 1.46/0.56    inference(forward_demodulation,[],[f207,f128])).
% 1.46/0.56  fof(f207,plain,(
% 1.46/0.56    ~r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | ~spl3_9),
% 1.46/0.56    inference(forward_demodulation,[],[f63,f138])).
% 1.46/0.56  fof(f63,plain,(
% 1.46/0.56    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 1.46/0.56    inference(cnf_transformation,[],[f52])).
% 1.46/0.56  fof(f52,plain,(
% 1.46/0.56    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 1.46/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f22,f51,f50,f49])).
% 1.46/0.56  fof(f49,plain,(
% 1.46/0.56    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f50,plain,(
% 1.46/0.56    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f51,plain,(
% 1.46/0.56    ? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 1.46/0.56    introduced(choice_axiom,[])).
% 1.46/0.56  fof(f22,plain,(
% 1.46/0.56    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 1.46/0.56    inference(flattening,[],[f21])).
% 1.46/0.56  fof(f21,plain,(
% 1.46/0.56    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 1.46/0.56    inference(ennf_transformation,[],[f20])).
% 1.46/0.56  fof(f20,negated_conjecture,(
% 1.46/0.56    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.46/0.56    inference(negated_conjecture,[],[f19])).
% 1.46/0.56  fof(f19,conjecture,(
% 1.46/0.56    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).
% 1.46/0.56  fof(f197,plain,(
% 1.46/0.56    spl3_17 | ~spl3_4 | ~spl3_5 | ~spl3_13),
% 1.46/0.56    inference(avatar_split_clause,[],[f185,f163,f113,f108,f194])).
% 1.46/0.56  fof(f185,plain,(
% 1.46/0.56    sK2 = k2_funct_1(k2_funct_1(sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_13)),
% 1.46/0.56    inference(subsumption_resolution,[],[f184,f165])).
% 1.46/0.56  fof(f184,plain,(
% 1.46/0.56    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | (~spl3_4 | ~spl3_5)),
% 1.46/0.56    inference(subsumption_resolution,[],[f183,f110])).
% 1.46/0.56  fof(f183,plain,(
% 1.46/0.56    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_5),
% 1.46/0.56    inference(resolution,[],[f69,f115])).
% 1.46/0.56  fof(f69,plain,(
% 1.46/0.56    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f32])).
% 1.46/0.56  fof(f32,plain,(
% 1.46/0.56    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.56    inference(flattening,[],[f31])).
% 1.46/0.56  fof(f31,plain,(
% 1.46/0.56    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f4])).
% 1.46/0.56  fof(f4,axiom,(
% 1.46/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 1.46/0.56  fof(f190,plain,(
% 1.46/0.56    spl3_16 | ~spl3_4 | ~spl3_5 | ~spl3_13),
% 1.46/0.56    inference(avatar_split_clause,[],[f182,f163,f113,f108,f187])).
% 1.46/0.56  fof(f182,plain,(
% 1.46/0.56    k2_funct_1(sK2) = k4_relat_1(sK2) | (~spl3_4 | ~spl3_5 | ~spl3_13)),
% 1.46/0.56    inference(subsumption_resolution,[],[f181,f165])).
% 1.46/0.56  fof(f181,plain,(
% 1.46/0.56    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_relat_1(sK2) | (~spl3_4 | ~spl3_5)),
% 1.46/0.56    inference(subsumption_resolution,[],[f180,f110])).
% 1.46/0.56  fof(f180,plain,(
% 1.46/0.56    k2_funct_1(sK2) = k4_relat_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_5),
% 1.46/0.56    inference(resolution,[],[f68,f115])).
% 1.46/0.56  fof(f68,plain,(
% 1.46/0.56    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(X0) = k4_relat_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f30])).
% 1.46/0.56  fof(f30,plain,(
% 1.46/0.56    ! [X0] : (k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.46/0.56    inference(flattening,[],[f29])).
% 1.46/0.56  fof(f29,plain,(
% 1.46/0.56    ! [X0] : ((k2_funct_1(X0) = k4_relat_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.46/0.56    inference(ennf_transformation,[],[f3])).
% 1.46/0.56  fof(f3,axiom,(
% 1.46/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(X0) = k4_relat_1(X0)))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d9_funct_1)).
% 1.46/0.56  fof(f173,plain,(
% 1.46/0.56    spl3_14 | ~spl3_11),
% 1.46/0.56    inference(avatar_split_clause,[],[f168,f149,f170])).
% 1.46/0.56  fof(f168,plain,(
% 1.46/0.56    v4_relat_1(sK2,k2_struct_0(sK0)) | ~spl3_11),
% 1.46/0.56    inference(resolution,[],[f79,f151])).
% 1.46/0.56  fof(f79,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v4_relat_1(X2,X0)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f41])).
% 1.46/0.56  fof(f41,plain,(
% 1.46/0.56    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.46/0.56    inference(ennf_transformation,[],[f5])).
% 1.46/0.56  fof(f5,axiom,(
% 1.46/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.46/0.56  fof(f166,plain,(
% 1.46/0.56    spl3_13 | ~spl3_11),
% 1.46/0.56    inference(avatar_split_clause,[],[f156,f149,f163])).
% 1.46/0.56  fof(f156,plain,(
% 1.46/0.56    v1_relat_1(sK2) | ~spl3_11),
% 1.46/0.56    inference(resolution,[],[f153,f151])).
% 1.46/0.56  fof(f153,plain,(
% 1.46/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | v1_relat_1(X0)) )),
% 1.46/0.56    inference(resolution,[],[f66,f70])).
% 1.46/0.56  fof(f70,plain,(
% 1.46/0.56    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 1.46/0.56    inference(cnf_transformation,[],[f2])).
% 1.46/0.56  fof(f2,axiom,(
% 1.46/0.56    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 1.46/0.56  fof(f66,plain,(
% 1.46/0.56    ( ! [X0,X1] : (~v1_relat_1(X0) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | v1_relat_1(X1)) )),
% 1.46/0.56    inference(cnf_transformation,[],[f26])).
% 1.46/0.56  fof(f26,plain,(
% 1.46/0.56    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 1.46/0.56    inference(ennf_transformation,[],[f1])).
% 1.46/0.56  fof(f1,axiom,(
% 1.46/0.56    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 1.46/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 1.46/0.56  fof(f161,plain,(
% 1.46/0.56    spl3_12 | ~spl3_7 | ~spl3_9),
% 1.46/0.56    inference(avatar_split_clause,[],[f155,f136,f126,f158])).
% 1.46/0.56  fof(f155,plain,(
% 1.46/0.56    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_7 | ~spl3_9)),
% 1.46/0.56    inference(forward_demodulation,[],[f154,f128])).
% 1.46/0.56  fof(f154,plain,(
% 1.46/0.56    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_9),
% 1.46/0.56    inference(forward_demodulation,[],[f61,f138])).
% 1.46/0.56  fof(f61,plain,(
% 1.46/0.56    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 1.46/0.56    inference(cnf_transformation,[],[f52])).
% 1.46/0.56  fof(f152,plain,(
% 1.46/0.56    spl3_11 | ~spl3_7 | ~spl3_9),
% 1.46/0.56    inference(avatar_split_clause,[],[f147,f136,f126,f149])).
% 1.46/0.56  fof(f147,plain,(
% 1.46/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_7 | ~spl3_9)),
% 1.46/0.56    inference(forward_demodulation,[],[f146,f128])).
% 1.46/0.56  fof(f146,plain,(
% 1.46/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_9),
% 1.46/0.56    inference(forward_demodulation,[],[f60,f138])).
% 1.46/0.56  fof(f60,plain,(
% 1.46/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.46/0.56    inference(cnf_transformation,[],[f52])).
% 1.46/0.56  fof(f145,plain,(
% 1.46/0.56    spl3_10 | ~spl3_8 | ~spl3_9),
% 1.46/0.56    inference(avatar_split_clause,[],[f140,f136,f131,f142])).
% 1.46/0.57  fof(f131,plain,(
% 1.46/0.57    spl3_8 <=> v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 1.46/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.46/0.57  fof(f140,plain,(
% 1.46/0.57    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_8 | ~spl3_9)),
% 1.46/0.57    inference(backward_demodulation,[],[f133,f138])).
% 1.46/0.57  fof(f133,plain,(
% 1.46/0.57    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_8),
% 1.46/0.57    inference(avatar_component_clause,[],[f131])).
% 1.46/0.57  fof(f139,plain,(
% 1.46/0.57    spl3_9 | ~spl3_3),
% 1.46/0.57    inference(avatar_split_clause,[],[f123,f103,f136])).
% 1.46/0.57  fof(f123,plain,(
% 1.46/0.57    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_3),
% 1.46/0.57    inference(resolution,[],[f64,f105])).
% 1.46/0.57  fof(f64,plain,(
% 1.46/0.57    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.46/0.57    inference(cnf_transformation,[],[f23])).
% 1.46/0.57  fof(f23,plain,(
% 1.46/0.57    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.46/0.57    inference(ennf_transformation,[],[f15])).
% 1.46/0.57  fof(f15,axiom,(
% 1.46/0.57    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.46/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.46/0.57  fof(f134,plain,(
% 1.46/0.57    spl3_8 | ~spl3_1 | ~spl3_6),
% 1.46/0.57    inference(avatar_split_clause,[],[f124,f118,f93,f131])).
% 1.46/0.57  fof(f118,plain,(
% 1.46/0.57    spl3_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.46/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.46/0.57  fof(f124,plain,(
% 1.46/0.57    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) | (~spl3_1 | ~spl3_6)),
% 1.46/0.57    inference(backward_demodulation,[],[f120,f122])).
% 1.46/0.57  fof(f122,plain,(
% 1.46/0.57    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_1),
% 1.46/0.57    inference(resolution,[],[f64,f95])).
% 1.46/0.57  fof(f120,plain,(
% 1.46/0.57    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_6),
% 1.46/0.57    inference(avatar_component_clause,[],[f118])).
% 1.46/0.57  fof(f129,plain,(
% 1.46/0.57    spl3_7 | ~spl3_1),
% 1.46/0.57    inference(avatar_split_clause,[],[f122,f93,f126])).
% 1.46/0.57  fof(f121,plain,(
% 1.46/0.57    spl3_6),
% 1.46/0.57    inference(avatar_split_clause,[],[f59,f118])).
% 1.46/0.57  fof(f59,plain,(
% 1.46/0.57    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.46/0.57    inference(cnf_transformation,[],[f52])).
% 1.46/0.57  fof(f116,plain,(
% 1.46/0.57    spl3_5),
% 1.46/0.57    inference(avatar_split_clause,[],[f62,f113])).
% 1.46/0.57  fof(f62,plain,(
% 1.46/0.57    v2_funct_1(sK2)),
% 1.46/0.57    inference(cnf_transformation,[],[f52])).
% 1.46/0.57  fof(f111,plain,(
% 1.46/0.57    spl3_4),
% 1.46/0.57    inference(avatar_split_clause,[],[f58,f108])).
% 1.46/0.57  fof(f58,plain,(
% 1.46/0.57    v1_funct_1(sK2)),
% 1.46/0.57    inference(cnf_transformation,[],[f52])).
% 1.46/0.57  fof(f106,plain,(
% 1.46/0.57    spl3_3),
% 1.46/0.57    inference(avatar_split_clause,[],[f57,f103])).
% 1.46/0.57  fof(f57,plain,(
% 1.46/0.57    l1_struct_0(sK1)),
% 1.46/0.57    inference(cnf_transformation,[],[f52])).
% 1.46/0.57  fof(f101,plain,(
% 1.46/0.57    ~spl3_2),
% 1.46/0.57    inference(avatar_split_clause,[],[f56,f98])).
% 1.46/0.57  fof(f56,plain,(
% 1.46/0.57    ~v2_struct_0(sK1)),
% 1.46/0.57    inference(cnf_transformation,[],[f52])).
% 1.46/0.57  fof(f96,plain,(
% 1.46/0.57    spl3_1),
% 1.46/0.57    inference(avatar_split_clause,[],[f55,f93])).
% 1.46/0.57  fof(f55,plain,(
% 1.46/0.57    l1_struct_0(sK0)),
% 1.46/0.57    inference(cnf_transformation,[],[f52])).
% 1.46/0.57  % SZS output end Proof for theBenchmark
% 1.46/0.57  % (11270)------------------------------
% 1.46/0.57  % (11270)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.46/0.57  % (11270)Termination reason: Refutation
% 1.46/0.57  
% 1.46/0.57  % (11270)Memory used [KB]: 6780
% 1.46/0.57  % (11270)Time elapsed: 0.125 s
% 1.46/0.57  % (11270)------------------------------
% 1.46/0.57  % (11270)------------------------------
% 1.46/0.57  % (11267)Success in time 0.206 s
%------------------------------------------------------------------------------
