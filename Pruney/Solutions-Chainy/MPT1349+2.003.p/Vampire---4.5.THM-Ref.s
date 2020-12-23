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
% DateTime   : Thu Dec  3 13:14:40 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 1.35s
% Verified   : 
% Statistics : Number of formulae       :  250 ( 577 expanded)
%              Number of leaves         :   55 ( 300 expanded)
%              Depth                    :   13
%              Number of atoms          : 1372 (2963 expanded)
%              Number of equality atoms :  161 ( 434 expanded)
%              Maximal formula depth    :   17 (   7 average)
%              Maximal term depth       :    6 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f875,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f83,f88,f93,f98,f103,f108,f113,f118,f127,f132,f137,f142,f147,f151,f259,f263,f267,f269,f272,f285,f292,f297,f338,f342,f346,f356,f371,f375,f387,f393,f417,f431,f437,f476,f482,f489,f639,f645,f665,f672,f706,f726,f731,f803,f828,f833,f874])).

% (25722)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f874,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)
    | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK3))
    | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK3)) != k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3))
    | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f833,plain,
    ( spl6_120
    | ~ spl6_14
    | ~ spl6_56 ),
    inference(avatar_split_clause,[],[f810,f435,f144,f830])).

fof(f830,plain,
    ( spl6_120
  <=> k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_120])])).

fof(f144,plain,
    ( spl6_14
  <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).

fof(f435,plain,
    ( spl6_56
  <=> ! [X0] :
        ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).

fof(f810,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK3))
    | ~ spl6_14
    | ~ spl6_56 ),
    inference(resolution,[],[f146,f436])).

fof(f436,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X0)) )
    | ~ spl6_56 ),
    inference(avatar_component_clause,[],[f435])).

fof(f146,plain,
    ( m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_14 ),
    inference(avatar_component_clause,[],[f144])).

fof(f828,plain,
    ( spl6_119
    | ~ spl6_14
    | ~ spl6_53 ),
    inference(avatar_split_clause,[],[f809,f415,f144,f825])).

fof(f825,plain,
    ( spl6_119
  <=> k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_119])])).

fof(f415,plain,
    ( spl6_53
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).

fof(f809,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)
    | ~ spl6_14
    | ~ spl6_53 ),
    inference(resolution,[],[f146,f416])).

fof(f416,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0) )
    | ~ spl6_53 ),
    inference(avatar_component_clause,[],[f415])).

fof(f803,plain,
    ( spl6_46
    | spl6_5
    | ~ spl6_29
    | ~ spl6_37
    | ~ spl6_38
    | ~ spl6_39
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_33
    | ~ spl6_34
    | ~ spl6_100
    | ~ spl6_104
    | ~ spl6_105 ),
    inference(avatar_split_clause,[],[f802,f728,f723,f703,f289,f282,f95,f90,f85,f80,f317,f313,f309,f248,f100,f368])).

fof(f368,plain,
    ( spl6_46
  <=> v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).

fof(f100,plain,
    ( spl6_5
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).

fof(f248,plain,
    ( spl6_29
  <=> v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).

fof(f309,plain,
    ( spl6_37
  <=> m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).

fof(f313,plain,
    ( spl6_38
  <=> v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).

fof(f317,plain,
    ( spl6_39
  <=> v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).

fof(f80,plain,
    ( spl6_1
  <=> l1_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).

fof(f85,plain,
    ( spl6_2
  <=> v2_pre_topc(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).

fof(f90,plain,
    ( spl6_3
  <=> l1_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).

fof(f95,plain,
    ( spl6_4
  <=> v2_pre_topc(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).

fof(f282,plain,
    ( spl6_33
  <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).

fof(f289,plain,
    ( spl6_34
  <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).

fof(f703,plain,
    ( spl6_100
  <=> k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).

fof(f723,plain,
    ( spl6_104
  <=> k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_104])])).

fof(f728,plain,
    ( spl6_105
  <=> k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_105])])).

fof(f802,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v2_struct_0(sK1)
    | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl6_33
    | ~ spl6_34
    | ~ spl6_100
    | ~ spl6_104
    | ~ spl6_105 ),
    inference(trivial_inequality_removal,[],[f801])).

fof(f801,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v2_struct_0(sK1)
    | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl6_33
    | ~ spl6_34
    | ~ spl6_100
    | ~ spl6_104
    | ~ spl6_105 ),
    inference(forward_demodulation,[],[f800,f291])).

fof(f291,plain,
    ( k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl6_34 ),
    inference(avatar_component_clause,[],[f289])).

fof(f800,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v2_struct_0(sK1)
    | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl6_33
    | ~ spl6_100
    | ~ spl6_104
    | ~ spl6_105 ),
    inference(trivial_inequality_removal,[],[f799])).

fof(f799,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v2_struct_0(sK1)
    | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl6_33
    | ~ spl6_100
    | ~ spl6_104
    | ~ spl6_105 ),
    inference(forward_demodulation,[],[f798,f284])).

fof(f284,plain,
    ( k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl6_33 ),
    inference(avatar_component_clause,[],[f282])).

fof(f798,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v2_struct_0(sK1)
    | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl6_100
    | ~ spl6_104
    | ~ spl6_105 ),
    inference(trivial_inequality_removal,[],[f797])).

fof(f797,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) != k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v2_struct_0(sK1)
    | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl6_100
    | ~ spl6_104
    | ~ spl6_105 ),
    inference(forward_demodulation,[],[f796,f730])).

fof(f730,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ spl6_105 ),
    inference(avatar_component_clause,[],[f728])).

fof(f796,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) != k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v2_struct_0(sK1)
    | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl6_100
    | ~ spl6_104 ),
    inference(forward_demodulation,[],[f795,f705])).

fof(f705,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ spl6_100 ),
    inference(avatar_component_clause,[],[f703])).

fof(f795,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v2_struct_0(sK1)
    | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl6_104 ),
    inference(superposition,[],[f62,f725])).

fof(f725,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | ~ spl6_104 ),
    inference(avatar_component_clause,[],[f723])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK4(X0,X1,X2))) != k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2)))
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ v2_funct_1(X2)
      | v2_struct_0(X0)
      | v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f27])).

% (25735)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
fof(f27,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0)
        & ~ v2_struct_0(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
                     => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_2)).

fof(f731,plain,
    ( spl6_105
    | ~ spl6_56
    | ~ spl6_98 ),
    inference(avatar_split_clause,[],[f693,f669,f435,f728])).

fof(f669,plain,
    ( spl6_98
  <=> m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).

fof(f693,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ spl6_56
    | ~ spl6_98 ),
    inference(resolution,[],[f671,f436])).

fof(f671,plain,
    ( m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ spl6_98 ),
    inference(avatar_component_clause,[],[f669])).

fof(f726,plain,
    ( spl6_104
    | ~ spl6_53
    | ~ spl6_98 ),
    inference(avatar_split_clause,[],[f692,f669,f415,f723])).

fof(f692,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))
    | ~ spl6_53
    | ~ spl6_98 ),
    inference(resolution,[],[f671,f416])).

fof(f706,plain,
    ( spl6_100
    | ~ spl6_15
    | ~ spl6_98 ),
    inference(avatar_split_clause,[],[f688,f669,f149,f703])).

fof(f149,plain,
    ( spl6_15
  <=> ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X3)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).

fof(f688,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))
    | ~ spl6_15
    | ~ spl6_98 ),
    inference(resolution,[],[f671,f150])).

fof(f150,plain,
    ( ! [X3] :
        ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X3)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3)) )
    | ~ spl6_15 ),
    inference(avatar_component_clause,[],[f149])).

fof(f672,plain,
    ( spl6_46
    | spl6_98
    | ~ spl6_29
    | spl6_5
    | ~ spl6_37
    | ~ spl6_38
    | ~ spl6_39
    | ~ spl6_1
    | ~ spl6_2
    | ~ spl6_3
    | ~ spl6_4
    | ~ spl6_33
    | ~ spl6_34 ),
    inference(avatar_split_clause,[],[f667,f289,f282,f95,f90,f85,f80,f317,f313,f309,f100,f248,f669,f368])).

fof(f667,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK1)
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl6_33
    | ~ spl6_34 ),
    inference(trivial_inequality_removal,[],[f666])).

fof(f666,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | v2_struct_0(sK1)
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl6_33
    | ~ spl6_34 ),
    inference(forward_demodulation,[],[f513,f284])).

fof(f513,plain,
    ( ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v2_struct_0(sK1)
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl6_34 ),
    inference(trivial_inequality_removal,[],[f512])).

fof(f512,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | v2_struct_0(sK1)
    | ~ v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))
    | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | ~ spl6_34 ),
    inference(superposition,[],[f61,f291])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
      | v2_struct_0(X0)
      | ~ v2_funct_1(X2)
      | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1)))
      | v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f665,plain,(
    spl6_94 ),
    inference(avatar_contradiction_clause,[],[f662])).

fof(f662,plain,
    ( $false
    | spl6_94 ),
    inference(unit_resulting_resolution,[],[f77,f644])).

fof(f644,plain,
    ( ~ r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))),k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))))
    | spl6_94 ),
    inference(avatar_component_clause,[],[f642])).

fof(f642,plain,
    ( spl6_94
  <=> r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))),k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).

fof(f77,plain,(
    ! [X1] : r1_tarski(X1,X1) ),
    inference(equality_resolution,[],[f72])).

fof(f72,plain,(
    ! [X0,X1] :
      ( r1_tarski(X1,X0)
      | X0 != X1 ) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0,X1] :
      ( X0 = X1
    <=> ( r1_tarski(X1,X0)
        & r1_tarski(X0,X1) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

fof(f645,plain,
    ( ~ spl6_94
    | spl6_64
    | ~ spl6_93 ),
    inference(avatar_split_clause,[],[f640,f636,f486,f642])).

fof(f486,plain,
    ( spl6_64
  <=> r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).

fof(f636,plain,
    ( spl6_93
  <=> k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_93])])).

fof(f640,plain,
    ( ~ r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))),k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))))
    | spl6_64
    | ~ spl6_93 ),
    inference(backward_demodulation,[],[f488,f638])).

fof(f638,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2)))
    | ~ spl6_93 ),
    inference(avatar_component_clause,[],[f636])).

fof(f488,plain,
    ( ~ r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))))
    | spl6_64 ),
    inference(avatar_component_clause,[],[f486])).

fof(f639,plain,
    ( spl6_5
    | ~ spl6_4
    | ~ spl6_3
    | ~ spl6_8
    | ~ spl6_7
    | ~ spl6_6
    | spl6_93
    | ~ spl6_55
    | spl6_63 ),
    inference(avatar_split_clause,[],[f634,f473,f429,f636,f105,f110,f115,f90,f95,f100])).

fof(f115,plain,
    ( spl6_8
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).

fof(f110,plain,
    ( spl6_7
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).

fof(f105,plain,
    ( spl6_6
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).

fof(f429,plain,
    ( spl6_55
  <=> ! [X1,X2] :
        ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,X1,X2))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,X1,X2)))
        | v5_pre_topc(X2,sK0,X1)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).

fof(f473,plain,
    ( spl6_63
  <=> v5_pre_topc(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).

fof(f634,plain,
    ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2)))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ l1_pre_topc(sK1)
    | ~ v2_pre_topc(sK1)
    | v2_struct_0(sK1)
    | ~ spl6_55
    | spl6_63 ),
    inference(resolution,[],[f430,f475])).

fof(f475,plain,
    ( ~ v5_pre_topc(sK2,sK0,sK1)
    | spl6_63 ),
    inference(avatar_component_clause,[],[f473])).

fof(f430,plain,
    ( ! [X2,X1] :
        ( v5_pre_topc(X2,sK0,X1)
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,X1,X2))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,X1,X2)))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ v1_funct_1(X2)
        | ~ l1_pre_topc(X1)
        | ~ v2_pre_topc(X1)
        | v2_struct_0(X1) )
    | ~ spl6_55 ),
    inference(avatar_component_clause,[],[f429])).

fof(f489,plain,
    ( ~ spl6_2
    | ~ spl6_64
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5
    | ~ spl6_1
    | spl6_63 ),
    inference(avatar_split_clause,[],[f483,f473,f80,f100,f95,f90,f115,f110,f105,f486,f85])).

fof(f483,plain,
    ( ~ l1_pre_topc(sK0)
    | v2_struct_0(sK1)
    | ~ v2_pre_topc(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))))
    | ~ v2_pre_topc(sK0)
    | spl6_63 ),
    inference(resolution,[],[f475,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK5(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2))))
      | ~ v2_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)))
                    | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | ~ v2_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v5_pre_topc(X2,X0,X1)
              <=> ! [X3] :
                    ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                   => r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tops_2)).

fof(f482,plain,
    ( ~ spl6_46
    | ~ spl6_3
    | ~ spl6_37
    | ~ spl6_38
    | ~ spl6_39
    | ~ spl6_1
    | spl6_62 ),
    inference(avatar_split_clause,[],[f480,f469,f80,f317,f313,f309,f90,f368])).

fof(f469,plain,
    ( spl6_62
  <=> v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).

fof(f480,plain,
    ( ~ l1_pre_topc(sK0)
    | ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ l1_pre_topc(sK1)
    | ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | spl6_62 ),
    inference(resolution,[],[f471,f57])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( v5_pre_topc(X2,X0,X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X0)
      | ~ v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f4])).

% (25717)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
fof(f4,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( l1_pre_topc(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
              <=> ( v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
                  & v5_pre_topc(X2,X0,X1)
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_2)).

fof(f471,plain,
    ( ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | spl6_62 ),
    inference(avatar_component_clause,[],[f469])).

fof(f476,plain,
    ( spl6_9
    | ~ spl6_62
    | ~ spl6_63
    | ~ spl6_10
    | ~ spl6_1
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_3
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f467,f134,f129,f90,f115,f110,f105,f80,f124,f473,f469,f120])).

fof(f120,plain,
    ( spl6_9
  <=> v3_tops_2(sK2,sK0,sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).

fof(f124,plain,
    ( spl6_10
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).

fof(f129,plain,
    ( spl6_11
  <=> k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).

fof(f134,plain,
    ( spl6_12
  <=> k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).

% (25714)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
fof(f467,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_funct_1(sK2)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | v3_tops_2(sK2,sK0,sK1)
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(trivial_inequality_removal,[],[f466])).

fof(f466,plain,
    ( k2_struct_0(sK0) != k2_struct_0(sK0)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_pre_topc(sK0)
    | ~ v2_funct_1(sK2)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | v3_tops_2(sK2,sK0,sK1)
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(forward_demodulation,[],[f465,f136])).

fof(f136,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | ~ spl6_12 ),
    inference(avatar_component_clause,[],[f134])).

fof(f465,plain,
    ( ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_funct_1(sK2)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | v3_tops_2(sK2,sK0,sK1)
    | ~ spl6_11 ),
    inference(trivial_inequality_removal,[],[f462])).

fof(f462,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | ~ l1_pre_topc(sK0)
    | ~ v2_funct_1(sK2)
    | ~ v5_pre_topc(sK2,sK0,sK1)
    | ~ v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | v3_tops_2(sK2,sK0,sK1)
    | ~ spl6_11 ),
    inference(superposition,[],[f59,f131])).

fof(f131,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    | ~ spl6_11 ),
    inference(avatar_component_clause,[],[f129])).

fof(f59,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_funct_1(X2)
      | ~ v5_pre_topc(X2,X0,X1)
      | ~ v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f437,plain,
    ( ~ spl6_1
    | spl6_56
    | ~ spl6_53 ),
    inference(avatar_split_clause,[],[f432,f415,f435,f80])).

fof(f432,plain,
    ( ! [X0] :
        ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X0))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_pre_topc(sK0) )
    | ~ spl6_53 ),
    inference(resolution,[],[f416,f70])).

fof(f70,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] :
      ( ( m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0)))
        & l1_pre_topc(X0) )
     => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).

fof(f431,plain,
    ( ~ spl6_2
    | ~ spl6_1
    | spl6_55
    | ~ spl6_15 ),
    inference(avatar_split_clause,[],[f425,f149,f429,f80,f85])).

fof(f425,plain,
    ( ! [X2,X1] :
        ( k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,X1,X2))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,X1,X2)))
        | ~ l1_pre_topc(sK0)
        | v2_struct_0(X1)
        | ~ v2_pre_topc(X1)
        | ~ l1_pre_topc(X1)
        | ~ v1_funct_1(X2)
        | ~ v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | ~ v2_pre_topc(sK0)
        | v5_pre_topc(X2,sK0,X1) )
    | ~ spl6_15 ),
    inference(resolution,[],[f150,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_pre_topc(X0)
      | v2_struct_0(X1)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v2_pre_topc(X0)
      | v5_pre_topc(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f417,plain,
    ( ~ spl6_10
    | ~ spl6_30
    | spl6_53
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_31
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f413,f129,f256,f115,f110,f105,f415,f252,f124])).

fof(f252,plain,
    ( spl6_30
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).

fof(f256,plain,
    ( spl6_31
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).

fof(f413,plain,
    ( ! [X0] :
        ( ~ l1_struct_0(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_struct_0(sK0)
        | ~ v2_funct_1(sK2)
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0) )
    | ~ spl6_11 ),
    inference(trivial_inequality_removal,[],[f410])).

fof(f410,plain,
    ( ! [X0] :
        ( k2_struct_0(sK1) != k2_struct_0(sK1)
        | ~ l1_struct_0(sK1)
        | ~ v1_funct_1(sK2)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        | ~ m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ l1_struct_0(sK0)
        | ~ v2_funct_1(sK2)
        | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0) )
    | ~ spl6_11 ),
    inference(superposition,[],[f50,f131])).

fof(f50,plain,(
    ! [X2,X0,X3,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
      | ~ l1_struct_0(X0)
      | ~ v2_funct_1(X2)
      | k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ! [X3] :
                  ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)
                  | ~ v2_funct_1(X2)
                  | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
                  | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => ! [X1] :
          ( l1_struct_0(X1)
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ! [X3] :
                  ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                 => ( ( v2_funct_1(X2)
                      & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                   => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tops_2)).

fof(f393,plain,
    ( ~ spl6_9
    | spl6_12
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f206,f115,f90,f80,f110,f105,f134,f120])).

fof(f206,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | ~ v3_tops_2(sK2,sK0,sK1)
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_8 ),
    inference(resolution,[],[f162,f92])).

fof(f92,plain,
    ( l1_pre_topc(sK1)
    | ~ spl6_3 ),
    inference(avatar_component_clause,[],[f90])).

fof(f162,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)
        | ~ v3_tops_2(sK2,sK0,X0) )
    | ~ spl6_1
    | ~ spl6_8 ),
    inference(resolution,[],[f160,f82])).

fof(f82,plain,
    ( l1_pre_topc(sK0)
    | ~ spl6_1 ),
    inference(avatar_component_clause,[],[f80])).

fof(f160,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK2)
        | ~ v3_tops_2(sK2,X1,X0) )
    | ~ spl6_8 ),
    inference(resolution,[],[f54,f117])).

fof(f117,plain,
    ( v1_funct_1(sK2)
    | ~ spl6_8 ),
    inference(avatar_component_clause,[],[f115])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0)
      | ~ v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f387,plain,
    ( spl6_48
    | ~ spl6_14
    | ~ spl6_45 ),
    inference(avatar_split_clause,[],[f377,f365,f144,f384])).

fof(f384,plain,
    ( spl6_48
  <=> k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK3)) = k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).

fof(f365,plain,
    ( spl6_45
  <=> ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X5)) = k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X5)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).

fof(f377,plain,
    ( k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK3)) = k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3))
    | ~ spl6_14
    | ~ spl6_45 ),
    inference(resolution,[],[f366,f146])).

% (25727)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
fof(f366,plain,
    ( ! [X5] :
        ( ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X5)) = k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X5)) )
    | ~ spl6_45 ),
    inference(avatar_component_clause,[],[f365])).

fof(f375,plain,
    ( ~ spl6_1
    | ~ spl6_9
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_3
    | spl6_5
    | spl6_46 ),
    inference(avatar_split_clause,[],[f373,f368,f100,f90,f115,f110,f105,f120,f80])).

fof(f373,plain,
    ( v2_struct_0(sK1)
    | ~ l1_pre_topc(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v3_tops_2(sK2,sK0,sK1)
    | ~ l1_pre_topc(sK0)
    | spl6_46 ),
    inference(resolution,[],[f370,f60])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
      | v2_struct_0(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v3_tops_2(X2,X0,X1)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
              | ~ v3_tops_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)
              | ~ v3_tops_2(X2,X0,X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_pre_topc(X1)
          | v2_struct_0(X1) )
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
               => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_tops_2)).

fof(f370,plain,
    ( ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
    | spl6_46 ),
    inference(avatar_component_clause,[],[f368])).

fof(f371,plain,
    ( spl6_45
    | ~ spl6_37
    | ~ spl6_46
    | ~ spl6_38
    | ~ spl6_39
    | ~ spl6_43 ),
    inference(avatar_split_clause,[],[f363,f354,f317,f313,f368,f309,f365])).

fof(f354,plain,
    ( spl6_43
  <=> ! [X1,X0] :
        ( ~ v3_tops_2(X0,sK1,sK0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1)) = k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,X1)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).

fof(f363,plain,
    ( ! [X5] :
        ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)
        | ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0)))
        | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X5)) = k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X5)) )
    | ~ spl6_39
    | ~ spl6_43 ),
    inference(resolution,[],[f355,f318])).

fof(f318,plain,
    ( v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl6_39 ),
    inference(avatar_component_clause,[],[f317])).

fof(f355,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ v3_tops_2(X0,sK1,sK0)
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1)) = k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,X1)) )
    | ~ spl6_43 ),
    inference(avatar_component_clause,[],[f354])).

fof(f356,plain,
    ( ~ spl6_1
    | spl6_43
    | ~ spl6_2
    | ~ spl6_35 ),
    inference(avatar_split_clause,[],[f351,f295,f85,f354,f80])).

fof(f295,plain,
    ( spl6_35
  <=> ! [X1,X0,X2] :
        ( ~ v2_pre_topc(X0)
        | ~ v3_tops_2(X1,sK1,X0)
        | k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0),X1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
        | ~ l1_pre_topc(X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).

fof(f351,plain,
    ( ! [X0,X1] :
        ( ~ v3_tops_2(X0,sK1,sK0)
        | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1)) = k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,X1))
        | ~ m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0)))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0))
        | ~ l1_pre_topc(sK0) )
    | ~ spl6_2
    | ~ spl6_35 ),
    inference(resolution,[],[f296,f87])).

fof(f87,plain,
    ( v2_pre_topc(sK0)
    | ~ spl6_2 ),
    inference(avatar_component_clause,[],[f85])).

fof(f296,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(X0)
        | ~ v3_tops_2(X1,sK1,X0)
        | k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0),X1,X2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
        | ~ l1_pre_topc(X0) )
    | ~ spl6_35 ),
    inference(avatar_component_clause,[],[f295])).

fof(f346,plain,
    ( ~ spl6_8
    | ~ spl6_6
    | ~ spl6_7
    | spl6_39 ),
    inference(avatar_split_clause,[],[f344,f317,f110,f105,f115])).

fof(f344,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | spl6_39 ),
    inference(resolution,[],[f319,f74])).

fof(f74,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_1(k2_tops_2(X0,X1,X2))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
        & v1_funct_1(k2_tops_2(X0,X1,X2)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).

fof(f319,plain,
    ( ~ v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl6_39 ),
    inference(avatar_component_clause,[],[f317])).

fof(f342,plain,
    ( ~ spl6_8
    | ~ spl6_6
    | ~ spl6_7
    | spl6_38 ),
    inference(avatar_split_clause,[],[f340,f313,f110,f105,f115])).

fof(f340,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | spl6_38 ),
    inference(resolution,[],[f315,f75])).

fof(f75,plain,(
    ! [X2,X0,X1] :
      ( v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f315,plain,
    ( ~ v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))
    | spl6_38 ),
    inference(avatar_component_clause,[],[f313])).

fof(f338,plain,
    ( ~ spl6_8
    | ~ spl6_6
    | ~ spl6_7
    | spl6_37 ),
    inference(avatar_split_clause,[],[f336,f309,f110,f105,f115])).

fof(f336,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ v1_funct_1(sK2)
    | spl6_37 ),
    inference(resolution,[],[f311,f76])).

fof(f76,plain,(
    ! [X2,X0,X1] :
      ( m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f311,plain,
    ( ~ m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | spl6_37 ),
    inference(avatar_component_clause,[],[f309])).

fof(f297,plain,
    ( spl6_35
    | ~ spl6_3
    | ~ spl6_4
    | spl6_5 ),
    inference(avatar_split_clause,[],[f293,f100,f95,f90,f295])).

fof(f293,plain,
    ( ! [X2,X0,X1] :
        ( ~ v2_pre_topc(sK1)
        | ~ l1_pre_topc(sK1)
        | ~ v2_pre_topc(X0)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_1(X1)
        | ~ v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0))
        | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0))))
        | ~ m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0)))
        | k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0),X1,X2))
        | ~ v3_tops_2(X1,sK1,X0) )
    | spl6_5 ),
    inference(resolution,[],[f63,f102])).

fof(f102,plain,
    ( ~ v2_struct_0(sK1)
    | spl6_5 ),
    inference(avatar_component_clause,[],[f100])).

fof(f63,plain,(
    ! [X2,X0,X3,X1] :
      ( v2_struct_0(X0)
      | ~ v2_pre_topc(X0)
      | ~ l1_pre_topc(X0)
      | ~ v2_pre_topc(X1)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))
      | k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
      | ~ v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f292,plain,
    ( spl6_34
    | ~ spl6_10
    | ~ spl6_30
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_31
    | spl6_5
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f287,f129,f100,f256,f115,f110,f105,f252,f124,f289])).

fof(f287,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK0)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl6_11 ),
    inference(trivial_inequality_removal,[],[f286])).

fof(f286,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK0)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl6_11 ),
    inference(superposition,[],[f52,f131])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X0)
      | ~ v2_funct_1(X2)
      | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ! [X2] :
              ( ( k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
                & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              | ~ v2_funct_1(X2)
              | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
              | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              | ~ v1_funct_1(X2) )
          | ~ l1_struct_0(X1)
          | v2_struct_0(X1) )
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f285,plain,
    ( spl6_33
    | ~ spl6_10
    | ~ spl6_30
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_31
    | spl6_5
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f280,f129,f100,f256,f115,f110,f105,f252,f124,f282])).

fof(f280,plain,
    ( v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK0)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl6_11 ),
    inference(trivial_inequality_removal,[],[f279])).

fof(f279,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK0)
    | ~ v2_funct_1(sK2)
    | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl6_11 ),
    inference(superposition,[],[f51,f131])).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | v2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X0)
      | ~ v2_funct_1(X2)
      | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f272,plain,
    ( ~ spl6_1
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_10 ),
    inference(avatar_contradiction_clause,[],[f270])).

fof(f270,plain,
    ( $false
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_9
    | spl6_10 ),
    inference(unit_resulting_resolution,[],[f117,f82,f92,f122,f112,f107,f125,f56])).

% (25719)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% (25732)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% (25713)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% (25720)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
fof(f56,plain,(
    ! [X2,X0,X1] :
      ( v2_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_pre_topc(X0)
      | ~ v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f125,plain,
    ( ~ v2_funct_1(sK2)
    | spl6_10 ),
    inference(avatar_component_clause,[],[f124])).

fof(f107,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl6_6 ),
    inference(avatar_component_clause,[],[f105])).

fof(f112,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl6_7 ),
    inference(avatar_component_clause,[],[f110])).

fof(f122,plain,
    ( v3_tops_2(sK2,sK0,sK1)
    | ~ spl6_9 ),
    inference(avatar_component_clause,[],[f120])).

fof(f269,plain,
    ( ~ spl6_9
    | spl6_11
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_8 ),
    inference(avatar_split_clause,[],[f238,f115,f90,f80,f110,f105,f129,f120])).

fof(f238,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    | ~ v3_tops_2(sK2,sK0,sK1)
    | ~ spl6_1
    | ~ spl6_3
    | ~ spl6_8 ),
    inference(resolution,[],[f230,f92])).

fof(f230,plain,
    ( ! [X0] :
        ( ~ l1_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0))))
        | k2_struct_0(X0) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2)
        | ~ v3_tops_2(sK2,sK0,X0) )
    | ~ spl6_1
    | ~ spl6_8 ),
    inference(resolution,[],[f203,f82])).

fof(f203,plain,
    ( ! [X0,X1] :
        ( ~ l1_pre_topc(X1)
        | ~ l1_pre_topc(X0)
        | ~ v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0))))
        | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK2)
        | ~ v3_tops_2(sK2,X1,X0) )
    | ~ spl6_8 ),
    inference(resolution,[],[f55,f117])).

fof(f55,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ l1_pre_topc(X1)
      | ~ l1_pre_topc(X0)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
      | ~ v3_tops_2(X2,X0,X1) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f267,plain,
    ( ~ spl6_3
    | spl6_31 ),
    inference(avatar_split_clause,[],[f265,f256,f90])).

fof(f265,plain,
    ( ~ l1_pre_topc(sK1)
    | spl6_31 ),
    inference(resolution,[],[f258,f53])).

fof(f53,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( l1_struct_0(X0)
      | ~ l1_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( l1_pre_topc(X0)
     => l1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).

fof(f258,plain,
    ( ~ l1_struct_0(sK1)
    | spl6_31 ),
    inference(avatar_component_clause,[],[f256])).

fof(f263,plain,
    ( ~ spl6_1
    | spl6_30 ),
    inference(avatar_split_clause,[],[f261,f252,f80])).

fof(f261,plain,
    ( ~ l1_pre_topc(sK0)
    | spl6_30 ),
    inference(resolution,[],[f254,f53])).

fof(f254,plain,
    ( ~ l1_struct_0(sK0)
    | spl6_30 ),
    inference(avatar_component_clause,[],[f252])).

fof(f259,plain,
    ( spl6_29
    | ~ spl6_10
    | ~ spl6_30
    | ~ spl6_6
    | ~ spl6_7
    | ~ spl6_8
    | ~ spl6_31
    | ~ spl6_11 ),
    inference(avatar_split_clause,[],[f246,f129,f256,f115,f110,f105,f252,f124,f248])).

fof(f246,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK0)
    | ~ v2_funct_1(sK2)
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl6_11 ),
    inference(trivial_inequality_removal,[],[f245])).

fof(f245,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | ~ l1_struct_0(sK1)
    | ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ l1_struct_0(sK0)
    | ~ v2_funct_1(sK2)
    | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | ~ spl6_11 ),
    inference(superposition,[],[f49,f131])).

fof(f49,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ l1_struct_0(X1)
      | ~ v1_funct_1(X2)
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ l1_struct_0(X0)
      | ~ v2_funct_1(X2)
      | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_tops_2)).

fof(f151,plain,
    ( spl6_9
    | spl6_15 ),
    inference(avatar_split_clause,[],[f35,f149,f120])).

fof(f35,plain,(
    ! [X3] :
      ( ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0)))
      | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X3)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3))
      | v3_tops_2(sK2,sK0,sK1) ) ),
    inference(cnf_transformation,[],[f15])).

fof(f15,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <~> ( ! [X3] :
                      ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(flattening,[],[f14])).

fof(f14,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( v3_tops_2(X2,X0,X1)
              <~> ( ! [X3] :
                      ( k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))
                      | ~ m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) )
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_pre_topc(X1)
          & v2_pre_topc(X1)
          & ~ v2_struct_0(X1) )
      & l1_pre_topc(X0)
      & v2_pre_topc(X0) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
    ~ ! [X0] :
        ( ( l1_pre_topc(X0)
          & v2_pre_topc(X0) )
       => ! [X1] :
            ( ( l1_pre_topc(X1)
              & v2_pre_topc(X1)
              & ~ v2_struct_0(X1) )
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( v3_tops_2(X2,X0,X1)
                <=> ( ! [X3] :
                        ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                       => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                    & v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                    & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
    ! [X0] :
      ( ( l1_pre_topc(X0)
        & v2_pre_topc(X0) )
     => ! [X1] :
          ( ( l1_pre_topc(X1)
            & v2_pre_topc(X1)
            & ~ v2_struct_0(X1) )
         => ! [X2] :
              ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
             => ( v3_tops_2(X2,X0,X1)
              <=> ( ! [X3] :
                      ( m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))
                     => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) )
                  & v2_funct_1(X2)
                  & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                  & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_2)).

fof(f147,plain,
    ( ~ spl6_9
    | spl6_14
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f36,f134,f129,f124,f144,f120])).

fof(f36,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))
    | ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f142,plain,
    ( ~ spl6_9
    | ~ spl6_13
    | ~ spl6_10
    | ~ spl6_11
    | ~ spl6_12 ),
    inference(avatar_split_clause,[],[f37,f134,f129,f124,f139,f120])).

fof(f139,plain,
    ( spl6_13
  <=> k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).

fof(f37,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0)
    | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))
    | ~ v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f137,plain,
    ( spl6_9
    | spl6_12 ),
    inference(avatar_split_clause,[],[f38,f134,f120])).

fof(f38,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f132,plain,
    ( spl6_9
    | spl6_11 ),
    inference(avatar_split_clause,[],[f39,f129,f120])).

fof(f39,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f127,plain,
    ( spl6_9
    | spl6_10 ),
    inference(avatar_split_clause,[],[f40,f124,f120])).

fof(f40,plain,
    ( v2_funct_1(sK2)
    | v3_tops_2(sK2,sK0,sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f118,plain,(
    spl6_8 ),
    inference(avatar_split_clause,[],[f41,f115])).

fof(f41,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f15])).

fof(f113,plain,(
    spl6_7 ),
    inference(avatar_split_clause,[],[f42,f110])).

fof(f42,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f15])).

fof(f108,plain,(
    spl6_6 ),
    inference(avatar_split_clause,[],[f43,f105])).

fof(f43,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f15])).

fof(f103,plain,(
    ~ spl6_5 ),
    inference(avatar_split_clause,[],[f44,f100])).

fof(f44,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f98,plain,(
    spl6_4 ),
    inference(avatar_split_clause,[],[f45,f95])).

fof(f45,plain,(
    v2_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f93,plain,(
    spl6_3 ),
    inference(avatar_split_clause,[],[f46,f90])).

fof(f46,plain,(
    l1_pre_topc(sK1) ),
    inference(cnf_transformation,[],[f15])).

fof(f88,plain,(
    spl6_2 ),
    inference(avatar_split_clause,[],[f47,f85])).

fof(f47,plain,(
    v2_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).

fof(f83,plain,(
    spl6_1 ),
    inference(avatar_split_clause,[],[f48,f80])).

fof(f48,plain,(
    l1_pre_topc(sK0) ),
    inference(cnf_transformation,[],[f15])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 10:47:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.21/0.46  % (25726)lrs-2_6_acc=on:afp=40000:afq=1.2:amm=sco:anc=none:bs=on:bsr=on:cond=on:fsr=off:fde=none:lcm=reverse:lma=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sp=reverse_arity:urr=ec_only_162 on theBenchmark
% 0.21/0.47  % (25734)ott+11_8:1_acc=model:afp=1000:afq=1.0:anc=none:bd=off:bsr=on:cond=on:gs=on:gsem=off:irw=on:lma=on:nm=16:nwc=1.5:sac=on:sp=occurrence:urr=on_104 on theBenchmark
% 0.21/0.49  % (25715)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_7 on theBenchmark
% 0.21/0.50  % (25731)dis+1010_5_add=large:afp=10000:afq=1.2:amm=off:bs=unit_only:bsr=on:bce=on:cond=fast:fsr=off:fde=none:gsp=input_only:gs=on:irw=on:lma=on:nm=4:newcnf=on:nwc=1.3:nicw=on:sos=all:sac=on:updr=off_34 on theBenchmark
% 0.21/0.51  % (25711)dis+10_1_add=off:afp=4000:afq=1.2:anc=none:br=off:cond=on:gs=on:irw=on:lcm=reverse:nwc=10:sd=10:ss=axioms:sos=theory:sac=on:sp=occurrence:urr=on_2 on theBenchmark
% 0.21/0.51  % (25733)lrs+3_64_add=large:afp=40000:afq=1.4:anc=none:bd=preordered:bsr=on:fde=unused:gs=on:gsaa=from_current:gsem=on:irw=on:lcm=predicate:lma=on:lwlo=on:nm=16:newcnf=on:nwc=1.2:stl=90:sos=theory_285 on theBenchmark
% 0.21/0.51  % (25718)lrs+4_3_av=off:br=off:nm=0:newcnf=on:nwc=1:stl=30:sp=occurrence:urr=on_32 on theBenchmark
% 0.21/0.51  % (25736)lrs+10_24_add=off:afr=on:afp=1000:afq=1.4:anc=none:bs=unit_only:gs=on:gsaa=from_current:gsem=on:lma=on:nm=2:nwc=1.1:stl=60:sac=on:uhcvi=on_364 on theBenchmark
% 0.21/0.51  % (25725)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.51  % (25712)dis+10_3_add=large:afp=10000:afq=1.0:amm=sco:anc=none:gsp=input_only:gs=on:gsem=off:lcm=reverse:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (25723)ott+4_32_av=off:bsr=on:cond=on:er=known:fsr=off:gsp=input_only:gs=on:gsem=on:irw=on:lma=on:nm=4:nwc=1.2:sos=theory_197 on theBenchmark
% 0.21/0.51  % (25724)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.52  % (25729)dis+1010_3:1_av=off:gsp=input_only:nm=6:nwc=1:sos=all:sp=occurrence_48 on theBenchmark
% 0.21/0.52  % (25730)lrs+4_24_av=off:bd=preordered:bsr=on:irw=on:lma=on:lwlo=on:nm=64:newcnf=on:nwc=1.1:stl=30:sos=theory:updr=off:uhcvi=on_220 on theBenchmark
% 0.21/0.52  % (25716)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.52  % (25721)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.52  % (25726)Refutation found. Thanks to Tanya!
% 0.21/0.52  % SZS status Theorem for theBenchmark
% 0.21/0.52  % SZS output start Proof for theBenchmark
% 0.21/0.52  fof(f875,plain,(
% 0.21/0.52    $false),
% 0.21/0.52    inference(avatar_sat_refutation,[],[f83,f88,f93,f98,f103,f108,f113,f118,f127,f132,f137,f142,f147,f151,f259,f263,f267,f269,f272,f285,f292,f297,f338,f342,f346,f356,f371,f375,f387,f393,f417,f431,f437,f476,f482,f489,f639,f645,f665,f672,f706,f726,f731,f803,f828,f833,f874])).
% 0.21/0.52  % (25722)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.52  fof(f874,plain,(
% 0.21/0.52    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) != k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK3)) | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK3)) != k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))),
% 0.21/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.52  fof(f833,plain,(
% 0.21/0.52    spl6_120 | ~spl6_14 | ~spl6_56),
% 0.21/0.52    inference(avatar_split_clause,[],[f810,f435,f144,f830])).
% 0.21/0.52  fof(f830,plain,(
% 0.21/0.52    spl6_120 <=> k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK3))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_120])])).
% 0.21/0.52  fof(f144,plain,(
% 0.21/0.52    spl6_14 <=> m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_14])])).
% 0.21/0.52  fof(f435,plain,(
% 0.21/0.52    spl6_56 <=> ! [X0] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_56])])).
% 0.21/0.52  fof(f810,plain,(
% 0.21/0.52    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK3)) | (~spl6_14 | ~spl6_56)),
% 0.21/0.52    inference(resolution,[],[f146,f436])).
% 0.21/0.52  fof(f436,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X0))) ) | ~spl6_56),
% 0.21/0.52    inference(avatar_component_clause,[],[f435])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_14),
% 0.21/0.52    inference(avatar_component_clause,[],[f144])).
% 0.21/0.52  fof(f828,plain,(
% 0.21/0.52    spl6_119 | ~spl6_14 | ~spl6_53),
% 0.21/0.52    inference(avatar_split_clause,[],[f809,f415,f144,f825])).
% 0.21/0.52  fof(f825,plain,(
% 0.21/0.52    spl6_119 <=> k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_119])])).
% 0.21/0.52  fof(f415,plain,(
% 0.21/0.52    spl6_53 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_53])])).
% 0.21/0.52  fof(f809,plain,(
% 0.21/0.52    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3) | (~spl6_14 | ~spl6_53)),
% 0.21/0.52    inference(resolution,[],[f146,f416])).
% 0.21/0.52  fof(f416,plain,(
% 0.21/0.52    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)) ) | ~spl6_53),
% 0.21/0.52    inference(avatar_component_clause,[],[f415])).
% 0.21/0.52  fof(f803,plain,(
% 0.21/0.52    spl6_46 | spl6_5 | ~spl6_29 | ~spl6_37 | ~spl6_38 | ~spl6_39 | ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_33 | ~spl6_34 | ~spl6_100 | ~spl6_104 | ~spl6_105),
% 0.21/0.52    inference(avatar_split_clause,[],[f802,f728,f723,f703,f289,f282,f95,f90,f85,f80,f317,f313,f309,f248,f100,f368])).
% 0.21/0.52  fof(f368,plain,(
% 0.21/0.52    spl6_46 <=> v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_46])])).
% 0.21/0.52  fof(f100,plain,(
% 0.21/0.52    spl6_5 <=> v2_struct_0(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_5])])).
% 0.21/0.52  fof(f248,plain,(
% 0.21/0.52    spl6_29 <=> v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_29])])).
% 0.21/0.52  fof(f309,plain,(
% 0.21/0.52    spl6_37 <=> m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_37])])).
% 0.21/0.52  fof(f313,plain,(
% 0.21/0.52    spl6_38 <=> v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_38])])).
% 0.21/0.52  fof(f317,plain,(
% 0.21/0.52    spl6_39 <=> v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_39])])).
% 0.21/0.52  fof(f80,plain,(
% 0.21/0.52    spl6_1 <=> l1_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_1])])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    spl6_2 <=> v2_pre_topc(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_2])])).
% 0.21/0.52  fof(f90,plain,(
% 0.21/0.52    spl6_3 <=> l1_pre_topc(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_3])])).
% 0.21/0.52  fof(f95,plain,(
% 0.21/0.52    spl6_4 <=> v2_pre_topc(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_4])])).
% 0.21/0.52  fof(f282,plain,(
% 0.21/0.52    spl6_33 <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_33])])).
% 0.21/0.52  fof(f289,plain,(
% 0.21/0.52    spl6_34 <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_34])])).
% 0.21/0.52  fof(f703,plain,(
% 0.21/0.52    spl6_100 <=> k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_100])])).
% 0.21/0.52  fof(f723,plain,(
% 0.21/0.52    spl6_104 <=> k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_104])])).
% 0.21/0.52  fof(f728,plain,(
% 0.21/0.52    spl6_105 <=> k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_105])])).
% 0.21/0.52  fof(f802,plain,(
% 0.21/0.52    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | v2_struct_0(sK1) | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | (~spl6_33 | ~spl6_34 | ~spl6_100 | ~spl6_104 | ~spl6_105)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f801])).
% 0.21/0.52  fof(f801,plain,(
% 0.21/0.52    k2_struct_0(sK0) != k2_struct_0(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | v2_struct_0(sK1) | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | (~spl6_33 | ~spl6_34 | ~spl6_100 | ~spl6_104 | ~spl6_105)),
% 0.21/0.52    inference(forward_demodulation,[],[f800,f291])).
% 0.21/0.52  fof(f291,plain,(
% 0.21/0.52    k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~spl6_34),
% 0.21/0.52    inference(avatar_component_clause,[],[f289])).
% 0.21/0.52  fof(f800,plain,(
% 0.21/0.52    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | v2_struct_0(sK1) | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | (~spl6_33 | ~spl6_100 | ~spl6_104 | ~spl6_105)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f799])).
% 0.21/0.52  fof(f799,plain,(
% 0.21/0.52    k2_struct_0(sK1) != k2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | v2_struct_0(sK1) | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | (~spl6_33 | ~spl6_100 | ~spl6_104 | ~spl6_105)),
% 0.21/0.52    inference(forward_demodulation,[],[f798,f284])).
% 0.21/0.52  fof(f284,plain,(
% 0.21/0.52    k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~spl6_33),
% 0.21/0.52    inference(avatar_component_clause,[],[f282])).
% 0.21/0.52  fof(f798,plain,(
% 0.21/0.52    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | v2_struct_0(sK1) | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | (~spl6_100 | ~spl6_104 | ~spl6_105)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f797])).
% 0.21/0.52  fof(f797,plain,(
% 0.21/0.52    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) != k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | v2_struct_0(sK1) | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | (~spl6_100 | ~spl6_104 | ~spl6_105)),
% 0.21/0.52    inference(forward_demodulation,[],[f796,f730])).
% 0.21/0.52  fof(f730,plain,(
% 0.21/0.52    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) | ~spl6_105),
% 0.21/0.52    inference(avatar_component_clause,[],[f728])).
% 0.21/0.52  fof(f796,plain,(
% 0.21/0.52    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) != k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | v2_struct_0(sK1) | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | (~spl6_100 | ~spl6_104)),
% 0.21/0.52    inference(forward_demodulation,[],[f795,f705])).
% 0.21/0.52  fof(f705,plain,(
% 0.21/0.52    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) | ~spl6_100),
% 0.21/0.52    inference(avatar_component_clause,[],[f703])).
% 0.21/0.52  fof(f795,plain,(
% 0.21/0.52    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | v2_struct_0(sK1) | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~spl6_104),
% 0.21/0.52    inference(superposition,[],[f62,f725])).
% 0.21/0.52  fof(f725,plain,(
% 0.21/0.52    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) | ~spl6_104),
% 0.21/0.52    inference(avatar_component_clause,[],[f723])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,sK4(X0,X1,X2))) != k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK4(X0,X1,X2))) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v2_funct_1(X2) | v2_struct_0(X0) | v3_tops_2(X2,X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f28,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (! [X3] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f27])).
% 0.21/0.52  % (25735)dis+2_128_add=large:afp=100000:afq=1.4:amm=sco:anc=none:lma=on:nm=2:newcnf=on:nwc=1:nicw=on:sas=z3:sos=theory:sac=on:updr=off_288 on theBenchmark
% 0.21/0.52  fof(f27,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (! [X3] : (k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0) & ~v2_struct_0(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) => k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_tops_2)).
% 0.21/0.52  fof(f731,plain,(
% 0.21/0.52    spl6_105 | ~spl6_56 | ~spl6_98),
% 0.21/0.52    inference(avatar_split_clause,[],[f693,f669,f435,f728])).
% 0.21/0.52  fof(f669,plain,(
% 0.21/0.52    spl6_98 <=> m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_98])])).
% 0.21/0.52  fof(f693,plain,(
% 0.21/0.52    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) | (~spl6_56 | ~spl6_98)),
% 0.21/0.52    inference(resolution,[],[f671,f436])).
% 0.21/0.52  fof(f671,plain,(
% 0.21/0.52    m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | ~spl6_98),
% 0.21/0.52    inference(avatar_component_clause,[],[f669])).
% 0.21/0.52  fof(f726,plain,(
% 0.21/0.52    spl6_104 | ~spl6_53 | ~spl6_98),
% 0.21/0.52    inference(avatar_split_clause,[],[f692,f669,f415,f723])).
% 0.21/0.52  fof(f692,plain,(
% 0.21/0.52    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) = k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) | (~spl6_53 | ~spl6_98)),
% 0.21/0.52    inference(resolution,[],[f671,f416])).
% 0.21/0.52  fof(f706,plain,(
% 0.21/0.52    spl6_100 | ~spl6_15 | ~spl6_98),
% 0.21/0.52    inference(avatar_split_clause,[],[f688,f669,f149,f703])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    spl6_15 <=> ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X3)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_15])])).
% 0.21/0.52  fof(f688,plain,(
% 0.21/0.52    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)))) | (~spl6_15 | ~spl6_98)),
% 0.21/0.52    inference(resolution,[],[f671,f150])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X3)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3))) ) | ~spl6_15),
% 0.21/0.52    inference(avatar_component_clause,[],[f149])).
% 0.21/0.52  fof(f672,plain,(
% 0.21/0.52    spl6_46 | spl6_98 | ~spl6_29 | spl6_5 | ~spl6_37 | ~spl6_38 | ~spl6_39 | ~spl6_1 | ~spl6_2 | ~spl6_3 | ~spl6_4 | ~spl6_33 | ~spl6_34),
% 0.21/0.52    inference(avatar_split_clause,[],[f667,f289,f282,f95,f90,f85,f80,f317,f313,f309,f100,f248,f669,f368])).
% 0.21/0.52  fof(f667,plain,(
% 0.21/0.52    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK1) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | (~spl6_33 | ~spl6_34)),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f666])).
% 0.21/0.52  fof(f666,plain,(
% 0.21/0.52    k2_struct_0(sK1) != k2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | v2_struct_0(sK1) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | (~spl6_33 | ~spl6_34)),
% 0.21/0.52    inference(forward_demodulation,[],[f513,f284])).
% 0.21/0.52  fof(f513,plain,(
% 0.21/0.52    ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | v2_struct_0(sK1) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~spl6_34),
% 0.21/0.52    inference(trivial_inequality_removal,[],[f512])).
% 0.21/0.52  fof(f512,plain,(
% 0.21/0.52    k2_struct_0(sK0) != k2_struct_0(sK0) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK0) | ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | v2_struct_0(sK1) | ~v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | m1_subset_1(sK4(sK1,sK0,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),k1_zfmisc_1(u1_struct_0(sK0))) | v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~spl6_34),
% 0.21/0.52    inference(superposition,[],[f61,f291])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | v2_struct_0(X0) | ~v2_funct_1(X2) | m1_subset_1(sK4(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X1))) | v3_tops_2(X2,X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f28])).
% 0.21/0.52  fof(f665,plain,(
% 0.21/0.52    spl6_94),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f662])).
% 0.21/0.52  fof(f662,plain,(
% 0.21/0.52    $false | spl6_94),
% 0.21/0.52    inference(unit_resulting_resolution,[],[f77,f644])).
% 0.21/0.52  fof(f644,plain,(
% 0.21/0.52    ~r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))),k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2)))) | spl6_94),
% 0.21/0.52    inference(avatar_component_clause,[],[f642])).
% 0.21/0.52  fof(f642,plain,(
% 0.21/0.52    spl6_94 <=> r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))),k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_94])])).
% 0.21/0.52  fof(f77,plain,(
% 0.21/0.52    ( ! [X1] : (r1_tarski(X1,X1)) )),
% 0.21/0.52    inference(equality_resolution,[],[f72])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X0,X1] : (r1_tarski(X1,X0) | X0 != X1) )),
% 0.21/0.52    inference(cnf_transformation,[],[f1])).
% 0.21/0.52  fof(f1,axiom,(
% 0.21/0.52    ! [X0,X1] : (X0 = X1 <=> (r1_tarski(X1,X0) & r1_tarski(X0,X1)))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).
% 0.21/0.52  fof(f645,plain,(
% 0.21/0.52    ~spl6_94 | spl6_64 | ~spl6_93),
% 0.21/0.52    inference(avatar_split_clause,[],[f640,f636,f486,f642])).
% 0.21/0.52  fof(f486,plain,(
% 0.21/0.52    spl6_64 <=> r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_64])])).
% 0.21/0.52  fof(f636,plain,(
% 0.21/0.52    spl6_93 <=> k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_93])])).
% 0.21/0.52  fof(f640,plain,(
% 0.21/0.52    ~r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))),k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2)))) | (spl6_64 | ~spl6_93)),
% 0.21/0.52    inference(backward_demodulation,[],[f488,f638])).
% 0.21/0.52  fof(f638,plain,(
% 0.21/0.52    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))) | ~spl6_93),
% 0.21/0.52    inference(avatar_component_clause,[],[f636])).
% 0.21/0.52  fof(f488,plain,(
% 0.21/0.52    ~r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2)))) | spl6_64),
% 0.21/0.52    inference(avatar_component_clause,[],[f486])).
% 0.21/0.52  fof(f639,plain,(
% 0.21/0.52    spl6_5 | ~spl6_4 | ~spl6_3 | ~spl6_8 | ~spl6_7 | ~spl6_6 | spl6_93 | ~spl6_55 | spl6_63),
% 0.21/0.52    inference(avatar_split_clause,[],[f634,f473,f429,f636,f105,f110,f115,f90,f95,f100])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    spl6_8 <=> v1_funct_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_8])])).
% 0.21/0.52  fof(f110,plain,(
% 0.21/0.52    spl6_7 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_7])])).
% 0.21/0.52  fof(f105,plain,(
% 0.21/0.52    spl6_6 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_6])])).
% 0.21/0.52  fof(f429,plain,(
% 0.21/0.52    spl6_55 <=> ! [X1,X2] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,X1,X2))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,X1,X2))) | v5_pre_topc(X2,sK0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_55])])).
% 0.21/0.52  fof(f473,plain,(
% 0.21/0.52    spl6_63 <=> v5_pre_topc(sK2,sK0,sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_63])])).
% 0.21/0.52  fof(f634,plain,(
% 0.21/0.52    k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~v1_funct_1(sK2) | ~l1_pre_topc(sK1) | ~v2_pre_topc(sK1) | v2_struct_0(sK1) | (~spl6_55 | spl6_63)),
% 0.21/0.52    inference(resolution,[],[f430,f475])).
% 0.21/0.52  fof(f475,plain,(
% 0.21/0.52    ~v5_pre_topc(sK2,sK0,sK1) | spl6_63),
% 0.21/0.52    inference(avatar_component_clause,[],[f473])).
% 0.21/0.52  fof(f430,plain,(
% 0.21/0.52    ( ! [X2,X1] : (v5_pre_topc(X2,sK0,X1) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,X1,X2))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) ) | ~spl6_55),
% 0.21/0.52    inference(avatar_component_clause,[],[f429])).
% 0.21/0.52  fof(f489,plain,(
% 0.21/0.52    ~spl6_2 | ~spl6_64 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_3 | ~spl6_4 | spl6_5 | ~spl6_1 | spl6_63),
% 0.21/0.52    inference(avatar_split_clause,[],[f483,f473,f80,f100,f95,f90,f115,f110,f105,f486,f85])).
% 0.21/0.52  fof(f483,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | v2_struct_0(sK1) | ~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~r1_tarski(k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,sK1,sK2))),k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,sK1,sK2)))) | ~v2_pre_topc(sK0) | spl6_63),
% 0.21/0.52    inference(resolution,[],[f475,f69])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,sK5(X0,X1,X2))),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,sK5(X0,X1,X2)))) | ~v2_pre_topc(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0) | ~v2_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((v5_pre_topc(X2,X0,X1) <=> ! [X3] : (r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | ~v2_pre_topc(X1) | v2_struct_0(X1))) | (~l1_pre_topc(X0) | ~v2_pre_topc(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f6])).
% 0.21/0.52  fof(f6,axiom,(
% 0.21/0.52    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v5_pre_topc(X2,X0,X1) <=> ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => r1_tarski(k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)),k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t57_tops_2)).
% 0.21/0.52  fof(f482,plain,(
% 0.21/0.52    ~spl6_46 | ~spl6_3 | ~spl6_37 | ~spl6_38 | ~spl6_39 | ~spl6_1 | spl6_62),
% 0.21/0.52    inference(avatar_split_clause,[],[f480,f469,f80,f317,f313,f309,f90,f368])).
% 0.21/0.52  fof(f469,plain,(
% 0.21/0.52    spl6_62 <=> v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl6_62])])).
% 0.21/0.52  fof(f480,plain,(
% 0.21/0.52    ~l1_pre_topc(sK0) | ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~l1_pre_topc(sK1) | ~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | spl6_62),
% 0.21/0.52    inference(resolution,[],[f471,f57])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v5_pre_topc(X2,X0,X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_pre_topc(X0) | ~v3_tops_2(X2,X0,X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f24])).
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(flattening,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_pre_topc(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f4])).
% 0.21/0.52  % (25717)lrs+1011_8_add=large:afp=100000:afq=1.1:er=filter:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:nwc=1:stl=30:sd=2:ss=axioms:st=1.5:sos=on_3 on theBenchmark
% 0.21/0.52  fof(f4,axiom,(
% 0.21/0.52    ! [X0] : (l1_pre_topc(X0) => ! [X1] : (l1_pre_topc(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) & v5_pre_topc(X2,X0,X1) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 0.21/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_tops_2)).
% 0.21/0.52  fof(f471,plain,(
% 0.21/0.52    ~v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | spl6_62),
% 0.21/0.52    inference(avatar_component_clause,[],[f469])).
% 0.21/0.52  fof(f476,plain,(
% 0.21/0.52    spl6_9 | ~spl6_62 | ~spl6_63 | ~spl6_10 | ~spl6_1 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_3 | ~spl6_11 | ~spl6_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f467,f134,f129,f90,f115,f110,f105,f80,f124,f473,f469,f120])).
% 0.21/0.53  fof(f120,plain,(
% 0.21/0.53    spl6_9 <=> v3_tops_2(sK2,sK0,sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_9])])).
% 0.21/0.53  fof(f124,plain,(
% 0.21/0.53    spl6_10 <=> v2_funct_1(sK2)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_10])])).
% 0.21/0.53  fof(f129,plain,(
% 0.21/0.53    spl6_11 <=> k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_11])])).
% 0.21/0.53  fof(f134,plain,(
% 0.21/0.53    spl6_12 <=> k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_12])])).
% 0.21/0.53  % (25714)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.53  fof(f467,plain,(
% 0.21/0.53    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_funct_1(sK2) | ~v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | v3_tops_2(sK2,sK0,sK1) | (~spl6_11 | ~spl6_12)),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f466])).
% 0.21/0.53  fof(f466,plain,(
% 0.21/0.53    k2_struct_0(sK0) != k2_struct_0(sK0) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_pre_topc(sK0) | ~v2_funct_1(sK2) | ~v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | v3_tops_2(sK2,sK0,sK1) | (~spl6_11 | ~spl6_12)),
% 0.21/0.53    inference(forward_demodulation,[],[f465,f136])).
% 0.21/0.53  fof(f136,plain,(
% 0.21/0.53    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0) | ~spl6_12),
% 0.21/0.53    inference(avatar_component_clause,[],[f134])).
% 0.21/0.53  fof(f465,plain,(
% 0.21/0.53    ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_funct_1(sK2) | ~v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | v3_tops_2(sK2,sK0,sK1) | ~spl6_11),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f462])).
% 0.21/0.53  fof(f462,plain,(
% 0.21/0.53    k2_struct_0(sK1) != k2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0) | ~l1_pre_topc(sK0) | ~v2_funct_1(sK2) | ~v5_pre_topc(sK2,sK0,sK1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | v3_tops_2(sK2,sK0,sK1) | ~spl6_11),
% 0.21/0.53    inference(superposition,[],[f59,f131])).
% 0.21/0.53  fof(f131,plain,(
% 0.21/0.53    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) | ~spl6_11),
% 0.21/0.53    inference(avatar_component_clause,[],[f129])).
% 0.21/0.53  fof(f59,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X0) | ~l1_pre_topc(X0) | ~v2_funct_1(X2) | ~v5_pre_topc(X2,X0,X1) | ~v5_pre_topc(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | v3_tops_2(X2,X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f437,plain,(
% 0.21/0.53    ~spl6_1 | spl6_56 | ~spl6_53),
% 0.21/0.53    inference(avatar_split_clause,[],[f432,f415,f435,f80])).
% 0.21/0.53  fof(f432,plain,(
% 0.21/0.53    ( ! [X0] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X0)) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X0)) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_pre_topc(sK0)) ) | ~spl6_53),
% 0.21/0.53    inference(resolution,[],[f416,f70])).
% 0.21/0.53  fof(f70,plain,(
% 0.21/0.53    ( ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f32])).
% 0.21/0.53  fof(f32,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f31])).
% 0.21/0.53  fof(f31,plain,(
% 0.21/0.53    ! [X0,X1] : (m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))) | (~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0)))),
% 0.21/0.53    inference(ennf_transformation,[],[f2])).
% 0.21/0.53  fof(f2,axiom,(
% 0.21/0.53    ! [X0,X1] : ((m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(X0))) & l1_pre_topc(X0)) => m1_subset_1(k2_pre_topc(X0,X1),k1_zfmisc_1(u1_struct_0(X0))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_pre_topc)).
% 0.21/0.53  fof(f431,plain,(
% 0.21/0.53    ~spl6_2 | ~spl6_1 | spl6_55 | ~spl6_15),
% 0.21/0.53    inference(avatar_split_clause,[],[f425,f149,f429,f80,f85])).
% 0.21/0.53  fof(f425,plain,(
% 0.21/0.53    ( ! [X2,X1] : (k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK5(sK0,X1,X2))) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK5(sK0,X1,X2))) | ~l1_pre_topc(sK0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | ~v2_pre_topc(sK0) | v5_pre_topc(X2,sK0,X1)) ) | ~spl6_15),
% 0.21/0.53    inference(resolution,[],[f150,f68])).
% 0.21/0.53  fof(f68,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (m1_subset_1(sK5(X0,X1,X2),k1_zfmisc_1(u1_struct_0(X0))) | ~l1_pre_topc(X0) | v2_struct_0(X1) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v2_pre_topc(X0) | v5_pre_topc(X2,X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f30])).
% 0.21/0.53  fof(f417,plain,(
% 0.21/0.53    ~spl6_10 | ~spl6_30 | spl6_53 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_31 | ~spl6_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f413,f129,f256,f115,f110,f105,f415,f252,f124])).
% 0.21/0.53  fof(f252,plain,(
% 0.21/0.53    spl6_30 <=> l1_struct_0(sK0)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_30])])).
% 0.21/0.53  fof(f256,plain,(
% 0.21/0.53    spl6_31 <=> l1_struct_0(sK1)),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_31])])).
% 0.21/0.53  fof(f413,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | ~v2_funct_1(sK2) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)) ) | ~spl6_11),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f410])).
% 0.21/0.53  fof(f410,plain,(
% 0.21/0.53    ( ! [X0] : (k2_struct_0(sK1) != k2_struct_0(sK1) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~m1_subset_1(X0,k1_zfmisc_1(u1_struct_0(sK0))) | ~l1_struct_0(sK0) | ~v2_funct_1(sK2) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X0) = k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X0)) ) | ~spl6_11),
% 0.21/0.53    inference(superposition,[],[f50,f131])).
% 0.21/0.53  fof(f50,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) | ~l1_struct_0(X0) | ~v2_funct_1(X2) | k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f19])).
% 0.21/0.53  fof(f19,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f18])).
% 0.21/0.53  fof(f18,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (! [X3] : ((k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f9])).
% 0.21/0.53  fof(f9,axiom,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3) = k8_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X3))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_tops_2)).
% 0.21/0.53  fof(f393,plain,(
% 0.21/0.53    ~spl6_9 | spl6_12 | ~spl6_6 | ~spl6_7 | ~spl6_1 | ~spl6_3 | ~spl6_8),
% 0.21/0.53    inference(avatar_split_clause,[],[f206,f115,f90,f80,f110,f105,f134,f120])).
% 0.21/0.53  fof(f206,plain,(
% 0.21/0.53    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0) | ~v3_tops_2(sK2,sK0,sK1) | (~spl6_1 | ~spl6_3 | ~spl6_8)),
% 0.21/0.53    inference(resolution,[],[f162,f92])).
% 0.21/0.53  fof(f92,plain,(
% 0.21/0.53    l1_pre_topc(sK1) | ~spl6_3),
% 0.21/0.53    inference(avatar_component_clause,[],[f90])).
% 0.21/0.53  fof(f162,plain,(
% 0.21/0.53    ( ! [X0] : (~l1_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | k2_struct_0(sK0) = k1_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) | ~v3_tops_2(sK2,sK0,X0)) ) | (~spl6_1 | ~spl6_8)),
% 0.21/0.53    inference(resolution,[],[f160,f82])).
% 0.21/0.53  fof(f82,plain,(
% 0.21/0.53    l1_pre_topc(sK0) | ~spl6_1),
% 0.21/0.53    inference(avatar_component_clause,[],[f80])).
% 0.21/0.53  fof(f160,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK2) | ~v3_tops_2(sK2,X1,X0)) ) | ~spl6_8),
% 0.21/0.53    inference(resolution,[],[f54,f117])).
% 0.21/0.53  fof(f117,plain,(
% 0.21/0.53    v1_funct_1(sK2) | ~spl6_8),
% 0.21/0.53    inference(avatar_component_clause,[],[f115])).
% 0.21/0.53  fof(f54,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0) | ~v3_tops_2(X2,X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f24])).
% 0.21/0.53  fof(f387,plain,(
% 0.21/0.53    spl6_48 | ~spl6_14 | ~spl6_45),
% 0.21/0.53    inference(avatar_split_clause,[],[f377,f365,f144,f384])).
% 0.21/0.53  fof(f384,plain,(
% 0.21/0.53    spl6_48 <=> k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK3)) = k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_48])])).
% 0.21/0.53  fof(f365,plain,(
% 0.21/0.53    spl6_45 <=> ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X5)) = k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X5)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_45])])).
% 0.21/0.53  fof(f377,plain,(
% 0.21/0.53    k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,sK3)) = k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK3)) | (~spl6_14 | ~spl6_45)),
% 0.21/0.53    inference(resolution,[],[f366,f146])).
% 0.21/0.53  % (25727)lrs+4_5:4_av=off:bd=off:er=filter:lma=on:lwlo=on:nwc=1:stl=30:sp=occurrence:updr=off_230 on theBenchmark
% 0.21/0.53  fof(f366,plain,(
% 0.21/0.53    ( ! [X5] : (~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X5)) = k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X5))) ) | ~spl6_45),
% 0.21/0.53    inference(avatar_component_clause,[],[f365])).
% 0.21/0.53  fof(f375,plain,(
% 0.21/0.53    ~spl6_1 | ~spl6_9 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_3 | spl6_5 | spl6_46),
% 0.21/0.53    inference(avatar_split_clause,[],[f373,f368,f100,f90,f115,f110,f105,f120,f80])).
% 0.21/0.53  fof(f373,plain,(
% 0.21/0.53    v2_struct_0(sK1) | ~l1_pre_topc(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v3_tops_2(sK2,sK0,sK1) | ~l1_pre_topc(sK0) | spl6_46),
% 0.21/0.53    inference(resolution,[],[f370,f60])).
% 0.21/0.53  fof(f60,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | v2_struct_0(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v3_tops_2(X2,X0,X1) | ~l1_pre_topc(X0)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f26])).
% 0.21/0.53  fof(f26,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_pre_topc(X1) | v2_struct_0(X1)) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(flattening,[],[f25])).
% 0.21/0.53  fof(f25,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0) | ~v3_tops_2(X2,X0,X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_pre_topc(X1) | v2_struct_0(X1))) | ~l1_pre_topc(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f10])).
% 0.21/0.53  fof(f10,axiom,(
% 0.21/0.53    ! [X0] : (l1_pre_topc(X0) => ! [X1] : ((l1_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) => v3_tops_2(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X1,X0)))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_tops_2)).
% 0.21/0.53  fof(f370,plain,(
% 0.21/0.53    ~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | spl6_46),
% 0.21/0.53    inference(avatar_component_clause,[],[f368])).
% 0.21/0.53  fof(f371,plain,(
% 0.21/0.53    spl6_45 | ~spl6_37 | ~spl6_46 | ~spl6_38 | ~spl6_39 | ~spl6_43),
% 0.21/0.53    inference(avatar_split_clause,[],[f363,f354,f317,f313,f368,f309,f365])).
% 0.21/0.53  fof(f354,plain,(
% 0.21/0.53    spl6_43 <=> ! [X1,X0] : (~v3_tops_2(X0,sK1,sK0) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v1_funct_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1)) = k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,X1)))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_43])])).
% 0.21/0.53  fof(f363,plain,(
% 0.21/0.53    ( ! [X5] : (~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | ~v3_tops_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK1,sK0) | ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(X5,k1_zfmisc_1(u1_struct_0(sK0))) | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k2_pre_topc(sK0,X5)) = k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),X5))) ) | (~spl6_39 | ~spl6_43)),
% 0.21/0.53    inference(resolution,[],[f355,f318])).
% 0.21/0.53  fof(f318,plain,(
% 0.21/0.53    v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~spl6_39),
% 0.21/0.53    inference(avatar_component_clause,[],[f317])).
% 0.21/0.53  fof(f355,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~v3_tops_2(X0,sK1,sK0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1)) = k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,X1))) ) | ~spl6_43),
% 0.21/0.53    inference(avatar_component_clause,[],[f354])).
% 0.21/0.53  fof(f356,plain,(
% 0.21/0.53    ~spl6_1 | spl6_43 | ~spl6_2 | ~spl6_35),
% 0.21/0.53    inference(avatar_split_clause,[],[f351,f295,f85,f354,f80])).
% 0.21/0.53  fof(f295,plain,(
% 0.21/0.53    spl6_35 <=> ! [X1,X0,X2] : (~v2_pre_topc(X0) | ~v3_tops_2(X1,sK1,X0) | k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0),X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~l1_pre_topc(X0))),
% 0.21/0.53    introduced(avatar_definition,[new_symbols(naming,[spl6_35])])).
% 0.21/0.53  fof(f351,plain,(
% 0.21/0.53    ( ! [X0,X1] : (~v3_tops_2(X0,sK1,sK0) | k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,k2_pre_topc(sK0,X1)) = k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),X0,X1)) | ~m1_subset_1(X1,k1_zfmisc_1(u1_struct_0(sK0))) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,u1_struct_0(sK1),u1_struct_0(sK0)) | ~l1_pre_topc(sK0)) ) | (~spl6_2 | ~spl6_35)),
% 0.21/0.53    inference(resolution,[],[f296,f87])).
% 0.21/0.53  fof(f87,plain,(
% 0.21/0.53    v2_pre_topc(sK0) | ~spl6_2),
% 0.21/0.53    inference(avatar_component_clause,[],[f85])).
% 0.21/0.53  fof(f296,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v2_pre_topc(X0) | ~v3_tops_2(X1,sK1,X0) | k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0),X1,X2)) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~l1_pre_topc(X0)) ) | ~spl6_35),
% 0.21/0.53    inference(avatar_component_clause,[],[f295])).
% 0.21/0.53  fof(f346,plain,(
% 0.21/0.53    ~spl6_8 | ~spl6_6 | ~spl6_7 | spl6_39),
% 0.21/0.53    inference(avatar_split_clause,[],[f344,f317,f110,f105,f115])).
% 0.21/0.53  fof(f344,plain,(
% 0.21/0.53    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | spl6_39),
% 0.21/0.53    inference(resolution,[],[f319,f74])).
% 0.21/0.53  fof(f74,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v1_funct_1(k2_tops_2(X0,X1,X2)) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f34,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.53    inference(flattening,[],[f33])).
% 0.21/0.53  fof(f33,plain,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.53    inference(ennf_transformation,[],[f5])).
% 0.21/0.53  fof(f5,axiom,(
% 0.21/0.53    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) & v1_funct_1(k2_tops_2(X0,X1,X2))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_k2_tops_2)).
% 0.21/0.53  fof(f319,plain,(
% 0.21/0.53    ~v1_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl6_39),
% 0.21/0.53    inference(avatar_component_clause,[],[f317])).
% 0.21/0.53  fof(f342,plain,(
% 0.21/0.53    ~spl6_8 | ~spl6_6 | ~spl6_7 | spl6_38),
% 0.21/0.53    inference(avatar_split_clause,[],[f340,f313,f110,f105,f115])).
% 0.21/0.53  fof(f340,plain,(
% 0.21/0.53    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | spl6_38),
% 0.21/0.53    inference(resolution,[],[f315,f75])).
% 0.21/0.53  fof(f75,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (v1_funct_2(k2_tops_2(X0,X1,X2),X1,X0) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f315,plain,(
% 0.21/0.53    ~v1_funct_2(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),u1_struct_0(sK1),u1_struct_0(sK0)) | spl6_38),
% 0.21/0.53    inference(avatar_component_clause,[],[f313])).
% 0.21/0.53  fof(f338,plain,(
% 0.21/0.53    ~spl6_8 | ~spl6_6 | ~spl6_7 | spl6_37),
% 0.21/0.53    inference(avatar_split_clause,[],[f336,f309,f110,f105,f115])).
% 0.21/0.53  fof(f336,plain,(
% 0.21/0.53    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~v1_funct_1(sK2) | spl6_37),
% 0.21/0.53    inference(resolution,[],[f311,f76])).
% 0.21/0.53  fof(f76,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (m1_subset_1(k2_tops_2(X0,X1,X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X0,X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f34])).
% 0.21/0.53  fof(f311,plain,(
% 0.21/0.53    ~m1_subset_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | spl6_37),
% 0.21/0.53    inference(avatar_component_clause,[],[f309])).
% 0.21/0.53  fof(f297,plain,(
% 0.21/0.53    spl6_35 | ~spl6_3 | ~spl6_4 | spl6_5),
% 0.21/0.53    inference(avatar_split_clause,[],[f293,f100,f95,f90,f295])).
% 0.21/0.53  fof(f293,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (~v2_pre_topc(sK1) | ~l1_pre_topc(sK1) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v1_funct_1(X1) | ~v1_funct_2(X1,u1_struct_0(sK1),u1_struct_0(X0)) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(X0)))) | ~m1_subset_1(X2,k1_zfmisc_1(u1_struct_0(X0))) | k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0),X1,k2_pre_topc(X0,X2)) = k2_pre_topc(sK1,k8_relset_1(u1_struct_0(sK1),u1_struct_0(X0),X1,X2)) | ~v3_tops_2(X1,sK1,X0)) ) | spl6_5),
% 0.21/0.53    inference(resolution,[],[f63,f102])).
% 0.21/0.53  fof(f102,plain,(
% 0.21/0.53    ~v2_struct_0(sK1) | spl6_5),
% 0.21/0.53    inference(avatar_component_clause,[],[f100])).
% 0.21/0.53  fof(f63,plain,(
% 0.21/0.53    ( ! [X2,X0,X3,X1] : (v2_struct_0(X0) | ~v2_pre_topc(X0) | ~l1_pre_topc(X0) | ~v2_pre_topc(X1) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X1))) | k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X1,X3)) = k2_pre_topc(X0,k8_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) | ~v3_tops_2(X2,X0,X1)) )),
% 0.21/0.53    inference(cnf_transformation,[],[f28])).
% 0.21/0.53  fof(f292,plain,(
% 0.21/0.53    spl6_34 | ~spl6_10 | ~spl6_30 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_31 | spl6_5 | ~spl6_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f287,f129,f100,f256,f115,f110,f105,f252,f124,f289])).
% 0.21/0.53  fof(f287,plain,(
% 0.21/0.53    v2_struct_0(sK1) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK0) | ~v2_funct_1(sK2) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~spl6_11),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f286])).
% 0.21/0.53  fof(f286,plain,(
% 0.21/0.53    k2_struct_0(sK1) != k2_struct_0(sK1) | v2_struct_0(sK1) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK0) | ~v2_funct_1(sK2) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~spl6_11),
% 0.21/0.53    inference(superposition,[],[f52,f131])).
% 0.21/0.53  fof(f52,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X0) | ~v2_funct_1(X2) | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f21,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : ((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1) | v2_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(flattening,[],[f20])).
% 0.21/0.53  fof(f20,plain,(
% 0.21/0.53    ! [X0] : (! [X1] : (! [X2] : (((k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | (~l1_struct_0(X1) | v2_struct_0(X1))) | ~l1_struct_0(X0))),
% 0.21/0.53    inference(ennf_transformation,[],[f7])).
% 0.21/0.53  fof(f7,axiom,(
% 0.21/0.53    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.21/0.53    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).
% 0.21/0.53  fof(f285,plain,(
% 0.21/0.53    spl6_33 | ~spl6_10 | ~spl6_30 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_31 | spl6_5 | ~spl6_11),
% 0.21/0.53    inference(avatar_split_clause,[],[f280,f129,f100,f256,f115,f110,f105,f252,f124,f282])).
% 0.21/0.53  fof(f280,plain,(
% 0.21/0.53    v2_struct_0(sK1) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK0) | ~v2_funct_1(sK2) | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~spl6_11),
% 0.21/0.53    inference(trivial_inequality_removal,[],[f279])).
% 0.21/0.53  fof(f279,plain,(
% 0.21/0.53    k2_struct_0(sK1) != k2_struct_0(sK1) | v2_struct_0(sK1) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK0) | ~v2_funct_1(sK2) | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~spl6_11),
% 0.21/0.53    inference(superposition,[],[f51,f131])).
% 0.21/0.53  fof(f51,plain,(
% 0.21/0.53    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | v2_struct_0(X1) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X0) | ~v2_funct_1(X2) | k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) )),
% 0.21/0.53    inference(cnf_transformation,[],[f21])).
% 0.21/0.53  fof(f272,plain,(
% 0.21/0.53    ~spl6_1 | ~spl6_3 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | spl6_10),
% 0.21/0.53    inference(avatar_contradiction_clause,[],[f270])).
% 0.21/0.53  fof(f270,plain,(
% 0.21/0.53    $false | (~spl6_1 | ~spl6_3 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_9 | spl6_10)),
% 0.21/0.53    inference(unit_resulting_resolution,[],[f117,f82,f92,f122,f112,f107,f125,f56])).
% 1.35/0.53  % (25719)dis+1011_4_av=off:cond=on:irw=on:lma=on:nm=2:nwc=1:sos=all:sp=occurrence_5 on theBenchmark
% 1.35/0.53  % (25732)dis+11_1024_av=off:bd=off:bs=on:cond=on:gs=on:lma=on:nm=16:nwc=1:sp=occurrence:updr=off_98 on theBenchmark
% 1.35/0.54  % (25713)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 1.35/0.54  % (25720)lrs+1002_4:1_aac=none:add=off:afr=on:afp=40000:afq=1.0:amm=off:anc=none:cond=on:fsr=off:fde=none:gs=on:gsaa=full_model:lma=on:nm=16:nwc=1:sas=z3:stl=30:sd=7:ss=axioms:sos=on:sp=occurrence:updr=off:uhcvi=on_85 on theBenchmark
% 1.35/0.54  fof(f56,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (v2_funct_1(X2) | ~l1_pre_topc(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_pre_topc(X0) | ~v3_tops_2(X2,X0,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f24])).
% 1.35/0.54  fof(f125,plain,(
% 1.35/0.54    ~v2_funct_1(sK2) | spl6_10),
% 1.35/0.54    inference(avatar_component_clause,[],[f124])).
% 1.35/0.54  fof(f107,plain,(
% 1.35/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl6_6),
% 1.35/0.54    inference(avatar_component_clause,[],[f105])).
% 1.35/0.54  fof(f112,plain,(
% 1.35/0.54    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl6_7),
% 1.35/0.54    inference(avatar_component_clause,[],[f110])).
% 1.35/0.54  fof(f122,plain,(
% 1.35/0.54    v3_tops_2(sK2,sK0,sK1) | ~spl6_9),
% 1.35/0.54    inference(avatar_component_clause,[],[f120])).
% 1.35/0.54  fof(f269,plain,(
% 1.35/0.54    ~spl6_9 | spl6_11 | ~spl6_6 | ~spl6_7 | ~spl6_1 | ~spl6_3 | ~spl6_8),
% 1.35/0.54    inference(avatar_split_clause,[],[f238,f115,f90,f80,f110,f105,f129,f120])).
% 1.35/0.54  fof(f238,plain,(
% 1.35/0.54    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) | ~v3_tops_2(sK2,sK0,sK1) | (~spl6_1 | ~spl6_3 | ~spl6_8)),
% 1.35/0.54    inference(resolution,[],[f230,f92])).
% 1.35/0.54  fof(f230,plain,(
% 1.35/0.54    ( ! [X0] : (~l1_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X0)))) | k2_struct_0(X0) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X0),sK2) | ~v3_tops_2(sK2,sK0,X0)) ) | (~spl6_1 | ~spl6_8)),
% 1.35/0.54    inference(resolution,[],[f203,f82])).
% 1.35/0.54  fof(f203,plain,(
% 1.35/0.54    ( ! [X0,X1] : (~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v1_funct_2(sK2,u1_struct_0(X1),u1_struct_0(X0)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X1),u1_struct_0(X0)))) | k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),sK2) | ~v3_tops_2(sK2,X1,X0)) ) | ~spl6_8),
% 1.35/0.54    inference(resolution,[],[f55,f117])).
% 1.35/0.54  fof(f55,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~l1_pre_topc(X1) | ~l1_pre_topc(X0) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) | ~v3_tops_2(X2,X0,X1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f24])).
% 1.35/0.54  fof(f267,plain,(
% 1.35/0.54    ~spl6_3 | spl6_31),
% 1.35/0.54    inference(avatar_split_clause,[],[f265,f256,f90])).
% 1.35/0.54  fof(f265,plain,(
% 1.35/0.54    ~l1_pre_topc(sK1) | spl6_31),
% 1.35/0.54    inference(resolution,[],[f258,f53])).
% 1.35/0.54  fof(f53,plain,(
% 1.35/0.54    ( ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f22])).
% 1.35/0.54  fof(f22,plain,(
% 1.35/0.54    ! [X0] : (l1_struct_0(X0) | ~l1_pre_topc(X0))),
% 1.35/0.54    inference(ennf_transformation,[],[f3])).
% 1.35/0.54  fof(f3,axiom,(
% 1.35/0.54    ! [X0] : (l1_pre_topc(X0) => l1_struct_0(X0))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',dt_l1_pre_topc)).
% 1.35/0.54  fof(f258,plain,(
% 1.35/0.54    ~l1_struct_0(sK1) | spl6_31),
% 1.35/0.54    inference(avatar_component_clause,[],[f256])).
% 1.35/0.54  fof(f263,plain,(
% 1.35/0.54    ~spl6_1 | spl6_30),
% 1.35/0.54    inference(avatar_split_clause,[],[f261,f252,f80])).
% 1.35/0.54  fof(f261,plain,(
% 1.35/0.54    ~l1_pre_topc(sK0) | spl6_30),
% 1.35/0.54    inference(resolution,[],[f254,f53])).
% 1.35/0.54  fof(f254,plain,(
% 1.35/0.54    ~l1_struct_0(sK0) | spl6_30),
% 1.35/0.54    inference(avatar_component_clause,[],[f252])).
% 1.35/0.54  fof(f259,plain,(
% 1.35/0.54    spl6_29 | ~spl6_10 | ~spl6_30 | ~spl6_6 | ~spl6_7 | ~spl6_8 | ~spl6_31 | ~spl6_11),
% 1.35/0.54    inference(avatar_split_clause,[],[f246,f129,f256,f115,f110,f105,f252,f124,f248])).
% 1.35/0.54  fof(f246,plain,(
% 1.35/0.54    ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK0) | ~v2_funct_1(sK2) | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~spl6_11),
% 1.35/0.54    inference(trivial_inequality_removal,[],[f245])).
% 1.35/0.54  fof(f245,plain,(
% 1.35/0.54    k2_struct_0(sK1) != k2_struct_0(sK1) | ~l1_struct_0(sK1) | ~v1_funct_1(sK2) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~l1_struct_0(sK0) | ~v2_funct_1(sK2) | v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | ~spl6_11),
% 1.35/0.54    inference(superposition,[],[f49,f131])).
% 1.35/0.54  fof(f49,plain,(
% 1.35/0.54    ( ! [X2,X0,X1] : (k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~l1_struct_0(X1) | ~v1_funct_1(X2) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~l1_struct_0(X0) | ~v2_funct_1(X2) | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) )),
% 1.35/0.54    inference(cnf_transformation,[],[f17])).
% 1.35/0.54  fof(f17,plain,(
% 1.35/0.54    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.35/0.54    inference(flattening,[],[f16])).
% 1.35/0.54  fof(f16,plain,(
% 1.35/0.54    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 1.35/0.54    inference(ennf_transformation,[],[f8])).
% 1.35/0.54  fof(f8,axiom,(
% 1.35/0.54    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_tops_2)).
% 1.35/0.54  fof(f151,plain,(
% 1.35/0.54    spl6_9 | spl6_15),
% 1.35/0.54    inference(avatar_split_clause,[],[f35,f149,f120])).
% 1.35/0.54  fof(f35,plain,(
% 1.35/0.54    ( ! [X3] : (~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(sK0))) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,X3)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,X3)) | v3_tops_2(sK2,sK0,sK1)) )),
% 1.35/0.54    inference(cnf_transformation,[],[f15])).
% 1.35/0.54  fof(f15,plain,(
% 1.35/0.54    ? [X0] : (? [X1] : (? [X2] : ((v3_tops_2(X2,X0,X1) <~> (! [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) & l1_pre_topc(X0) & v2_pre_topc(X0))),
% 1.35/0.54    inference(flattening,[],[f14])).
% 1.35/0.54  fof(f14,plain,(
% 1.35/0.54    ? [X0] : (? [X1] : (? [X2] : ((v3_tops_2(X2,X0,X1) <~> (! [X3] : (k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3)) | ~m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0)))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1))) & (l1_pre_topc(X0) & v2_pre_topc(X0)))),
% 1.35/0.54    inference(ennf_transformation,[],[f13])).
% 1.35/0.54  fof(f13,negated_conjecture,(
% 1.35/0.54    ~! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 1.35/0.54    inference(negated_conjecture,[],[f12])).
% 1.35/0.54  fof(f12,conjecture,(
% 1.35/0.54    ! [X0] : ((l1_pre_topc(X0) & v2_pre_topc(X0)) => ! [X1] : ((l1_pre_topc(X1) & v2_pre_topc(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => (v3_tops_2(X2,X0,X1) <=> (! [X3] : (m1_subset_1(X3,k1_zfmisc_1(u1_struct_0(X0))) => k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,k2_pre_topc(X0,X3)) = k2_pre_topc(X1,k7_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2,X3))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X0))))))),
% 1.35/0.54    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t74_tops_2)).
% 1.35/0.54  fof(f147,plain,(
% 1.35/0.54    ~spl6_9 | spl6_14 | ~spl6_10 | ~spl6_11 | ~spl6_12),
% 1.35/0.54    inference(avatar_split_clause,[],[f36,f134,f129,f124,f144,f120])).
% 1.35/0.54  fof(f36,plain,(
% 1.35/0.54    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | m1_subset_1(sK3,k1_zfmisc_1(u1_struct_0(sK0))) | ~v3_tops_2(sK2,sK0,sK1)),
% 1.35/0.54    inference(cnf_transformation,[],[f15])).
% 1.35/0.54  fof(f142,plain,(
% 1.35/0.54    ~spl6_9 | ~spl6_13 | ~spl6_10 | ~spl6_11 | ~spl6_12),
% 1.35/0.54    inference(avatar_split_clause,[],[f37,f134,f129,f124,f139,f120])).
% 1.35/0.54  fof(f139,plain,(
% 1.35/0.54    spl6_13 <=> k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) = k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3))),
% 1.35/0.54    introduced(avatar_definition,[new_symbols(naming,[spl6_13])])).
% 1.35/0.54  fof(f37,plain,(
% 1.35/0.54    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK0) | k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,k2_pre_topc(sK0,sK3)) != k2_pre_topc(sK1,k7_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2,sK3)) | ~v3_tops_2(sK2,sK0,sK1)),
% 1.35/0.54    inference(cnf_transformation,[],[f15])).
% 1.35/0.54  fof(f137,plain,(
% 1.35/0.54    spl6_9 | spl6_12),
% 1.35/0.54    inference(avatar_split_clause,[],[f38,f134,f120])).
% 1.35/0.54  fof(f38,plain,(
% 1.35/0.54    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK0) | v3_tops_2(sK2,sK0,sK1)),
% 1.35/0.54    inference(cnf_transformation,[],[f15])).
% 1.35/0.54  fof(f132,plain,(
% 1.35/0.54    spl6_9 | spl6_11),
% 1.35/0.54    inference(avatar_split_clause,[],[f39,f129,f120])).
% 1.35/0.54  fof(f39,plain,(
% 1.35/0.54    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_struct_0(sK1) | v3_tops_2(sK2,sK0,sK1)),
% 1.35/0.54    inference(cnf_transformation,[],[f15])).
% 1.35/0.54  fof(f127,plain,(
% 1.35/0.54    spl6_9 | spl6_10),
% 1.35/0.54    inference(avatar_split_clause,[],[f40,f124,f120])).
% 1.35/0.54  fof(f40,plain,(
% 1.35/0.54    v2_funct_1(sK2) | v3_tops_2(sK2,sK0,sK1)),
% 1.35/0.54    inference(cnf_transformation,[],[f15])).
% 1.35/0.54  fof(f118,plain,(
% 1.35/0.54    spl6_8),
% 1.35/0.54    inference(avatar_split_clause,[],[f41,f115])).
% 1.35/0.54  fof(f41,plain,(
% 1.35/0.54    v1_funct_1(sK2)),
% 1.35/0.54    inference(cnf_transformation,[],[f15])).
% 1.35/0.54  fof(f113,plain,(
% 1.35/0.54    spl6_7),
% 1.35/0.54    inference(avatar_split_clause,[],[f42,f110])).
% 1.35/0.54  fof(f42,plain,(
% 1.35/0.54    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.35/0.54    inference(cnf_transformation,[],[f15])).
% 1.35/0.54  fof(f108,plain,(
% 1.35/0.54    spl6_6),
% 1.35/0.54    inference(avatar_split_clause,[],[f43,f105])).
% 1.35/0.54  fof(f43,plain,(
% 1.35/0.54    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.35/0.54    inference(cnf_transformation,[],[f15])).
% 1.35/0.54  fof(f103,plain,(
% 1.35/0.54    ~spl6_5),
% 1.35/0.54    inference(avatar_split_clause,[],[f44,f100])).
% 1.35/0.54  fof(f44,plain,(
% 1.35/0.54    ~v2_struct_0(sK1)),
% 1.35/0.54    inference(cnf_transformation,[],[f15])).
% 1.35/0.54  fof(f98,plain,(
% 1.35/0.54    spl6_4),
% 1.35/0.54    inference(avatar_split_clause,[],[f45,f95])).
% 1.35/0.54  fof(f45,plain,(
% 1.35/0.54    v2_pre_topc(sK1)),
% 1.35/0.54    inference(cnf_transformation,[],[f15])).
% 1.35/0.54  fof(f93,plain,(
% 1.35/0.54    spl6_3),
% 1.35/0.54    inference(avatar_split_clause,[],[f46,f90])).
% 1.35/0.54  fof(f46,plain,(
% 1.35/0.54    l1_pre_topc(sK1)),
% 1.35/0.54    inference(cnf_transformation,[],[f15])).
% 1.35/0.54  fof(f88,plain,(
% 1.35/0.54    spl6_2),
% 1.35/0.54    inference(avatar_split_clause,[],[f47,f85])).
% 1.35/0.54  fof(f47,plain,(
% 1.35/0.54    v2_pre_topc(sK0)),
% 1.35/0.54    inference(cnf_transformation,[],[f15])).
% 1.35/0.54  fof(f83,plain,(
% 1.35/0.54    spl6_1),
% 1.35/0.54    inference(avatar_split_clause,[],[f48,f80])).
% 1.35/0.54  fof(f48,plain,(
% 1.35/0.54    l1_pre_topc(sK0)),
% 1.35/0.54    inference(cnf_transformation,[],[f15])).
% 1.35/0.54  % SZS output end Proof for theBenchmark
% 1.35/0.54  % (25726)------------------------------
% 1.35/0.54  % (25726)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.35/0.54  % (25726)Termination reason: Refutation
% 1.35/0.54  
% 1.35/0.54  % (25726)Memory used [KB]: 7164
% 1.35/0.54  % (25726)Time elapsed: 0.113 s
% 1.35/0.54  % (25726)------------------------------
% 1.35/0.54  % (25726)------------------------------
% 1.35/0.54  % (25710)Success in time 0.191 s
%------------------------------------------------------------------------------
