%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:30 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  322 ( 723 expanded)
%              Number of leaves         :   66 ( 344 expanded)
%              Depth                    :   24
%              Number of atoms          : 1484 (2980 expanded)
%              Number of equality atoms :  191 ( 504 expanded)
%              Maximal formula depth    :   14 (   6 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f721,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f79,f83,f87,f91,f95,f99,f103,f107,f111,f117,f121,f133,f135,f140,f145,f172,f176,f180,f202,f216,f235,f241,f261,f269,f277,f282,f296,f311,f319,f341,f362,f370,f391,f417,f428,f434,f435,f458,f472,f477,f556,f617,f655,f698,f703,f708,f713,f717])).

fof(f717,plain,
    ( ~ spl3_39
    | ~ spl3_6
    | ~ spl3_43
    | ~ spl3_85 ),
    inference(avatar_split_clause,[],[f715,f711,f339,f97,f314])).

fof(f314,plain,
    ( spl3_39
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f97,plain,
    ( spl3_6
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f339,plain,
    ( spl3_43
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f711,plain,
    ( spl3_85
  <=> ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_85])])).

fof(f715,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_43
    | ~ spl3_85 ),
    inference(resolution,[],[f712,f340])).

fof(f340,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f339])).

fof(f712,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) )
    | ~ spl3_85 ),
    inference(avatar_component_clause,[],[f711])).

fof(f713,plain,
    ( ~ spl3_6
    | ~ spl3_39
    | ~ spl3_43
    | spl3_85
    | spl3_84 ),
    inference(avatar_split_clause,[],[f709,f706,f711,f339,f314,f97])).

fof(f706,plain,
    ( spl3_84
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).

fof(f709,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
        | ~ v1_funct_1(sK2) )
    | spl3_84 ),
    inference(resolution,[],[f707,f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f707,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | spl3_84 ),
    inference(avatar_component_clause,[],[f706])).

fof(f708,plain,
    ( ~ spl3_16
    | ~ spl3_6
    | ~ spl3_2
    | ~ spl3_84
    | spl3_83 ),
    inference(avatar_split_clause,[],[f704,f701,f706,f81,f97,f156])).

fof(f156,plain,
    ( spl3_16
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f81,plain,
    ( spl3_2
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f701,plain,
    ( spl3_83
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).

fof(f704,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_83 ),
    inference(superposition,[],[f702,f60])).

fof(f60,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f26])).

fof(f26,plain,(
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

fof(f702,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2)
    | spl3_83 ),
    inference(avatar_component_clause,[],[f701])).

fof(f703,plain,
    ( ~ spl3_83
    | spl3_52
    | ~ spl3_82 ),
    inference(avatar_split_clause,[],[f699,f696,f470,f701])).

fof(f470,plain,
    ( spl3_52
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f696,plain,
    ( spl3_82
  <=> k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).

fof(f699,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2)
    | spl3_52
    | ~ spl3_82 ),
    inference(superposition,[],[f471,f697])).

fof(f697,plain,
    ( k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_82 ),
    inference(avatar_component_clause,[],[f696])).

fof(f471,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)
    | spl3_52 ),
    inference(avatar_component_clause,[],[f470])).

fof(f698,plain,
    ( spl3_82
    | ~ spl3_48
    | ~ spl3_46
    | ~ spl3_49
    | ~ spl3_74 ),
    inference(avatar_split_clause,[],[f694,f615,f415,f389,f409,f696])).

fof(f409,plain,
    ( spl3_48
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).

fof(f389,plain,
    ( spl3_46
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f415,plain,
    ( spl3_49
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f615,plain,
    ( spl3_74
  <=> ! [X9,X8] :
        ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X8,X9,k2_funct_1(sK2))
        | ~ v1_funct_2(k2_funct_1(sK2),X8,X9)
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | k2_relset_1(X8,X9,k2_funct_1(sK2)) != X9 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).

fof(f694,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_46
    | ~ spl3_49
    | ~ spl3_74 ),
    inference(trivial_inequality_removal,[],[f693])).

fof(f693,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_46
    | ~ spl3_49
    | ~ spl3_74 ),
    inference(forward_demodulation,[],[f692,f416])).

fof(f416,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f415])).

fof(f692,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_46
    | ~ spl3_74 ),
    inference(resolution,[],[f616,f390])).

fof(f390,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f389])).

fof(f616,plain,
    ( ! [X8,X9] :
        ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | ~ v1_funct_2(k2_funct_1(sK2),X8,X9)
        | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X8,X9,k2_funct_1(sK2))
        | k2_relset_1(X8,X9,k2_funct_1(sK2)) != X9 )
    | ~ spl3_74 ),
    inference(avatar_component_clause,[],[f615])).

fof(f655,plain,
    ( ~ spl3_39
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f654,f275,f267,f205,f119,f115,f89,f85,f314])).

fof(f85,plain,
    ( spl3_3
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f89,plain,
    ( spl3_4
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f115,plain,
    ( spl3_10
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f119,plain,
    ( spl3_11
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f205,plain,
    ( spl3_24
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f267,plain,
    ( spl3_33
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f275,plain,
    ( spl3_35
  <=> ! [X1,X0] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f654,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_35 ),
    inference(trivial_inequality_removal,[],[f653])).

fof(f653,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f652,f206])).

fof(f206,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f205])).

fof(f652,plain,
    ( k2_struct_0(sK1) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f651,f116])).

fof(f116,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f115])).

fof(f651,plain,
    ( u1_struct_0(sK1) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f650,f206])).

fof(f650,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f649,f86])).

fof(f86,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f85])).

fof(f649,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f648,f268])).

fof(f268,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f267])).

fof(f648,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f647,f120])).

fof(f120,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f119])).

fof(f647,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_24
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f646,f206])).

fof(f646,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f643,f116])).

fof(f643,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_35 ),
    inference(resolution,[],[f276,f90])).

fof(f90,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f89])).

fof(f276,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_relset_1(X0,X1,sK2) != X1 )
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f275])).

fof(f617,plain,
    ( ~ spl3_34
    | spl3_74
    | ~ spl3_62 ),
    inference(avatar_split_clause,[],[f584,f554,f615,f272])).

fof(f272,plain,
    ( spl3_34
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).

fof(f554,plain,
    ( spl3_62
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).

fof(f584,plain,
    ( ! [X8,X9] :
        ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X8,X9,k2_funct_1(sK2))
        | k2_relset_1(X8,X9,k2_funct_1(sK2)) != X9
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X8,X9)))
        | ~ v1_funct_2(k2_funct_1(sK2),X8,X9)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
    | ~ spl3_62 ),
    inference(resolution,[],[f555,f73])).

fof(f73,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f38])).

fof(f38,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
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
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f555,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_62 ),
    inference(avatar_component_clause,[],[f554])).

fof(f556,plain,
    ( ~ spl3_43
    | ~ spl3_39
    | spl3_62
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_36
    | ~ spl3_51
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f552,f475,f456,f285,f267,f205,f119,f115,f109,f101,f554,f314,f339])).

fof(f101,plain,
    ( spl3_7
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f109,plain,
    ( spl3_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f285,plain,
    ( spl3_36
  <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).

fof(f456,plain,
    ( spl3_51
  <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f475,plain,
    ( spl3_53
  <=> ! [X1,X0] :
        ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2))
        | ~ l1_struct_0(X0)
        | ~ l1_struct_0(X1)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f552,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_36
    | ~ spl3_51
    | ~ spl3_53 ),
    inference(trivial_inequality_removal,[],[f551])).

fof(f551,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_36
    | ~ spl3_51
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f550,f286])).

fof(f286,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_36 ),
    inference(avatar_component_clause,[],[f285])).

fof(f550,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_51
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f549,f206])).

fof(f549,plain,
    ( k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2)
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_51
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f548,f116])).

fof(f548,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_51
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f547,f457])).

fof(f457,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f456])).

fof(f547,plain,
    ( v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f546,f206])).

fof(f546,plain,
    ( v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f545,f116])).

fof(f545,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f544,f206])).

fof(f544,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f543,f116])).

fof(f543,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f542,f206])).

fof(f542,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_33
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f540,f116])).

fof(f540,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1))
    | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2)
    | ~ spl3_7
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_33
    | ~ spl3_53 ),
    inference(resolution,[],[f495,f102])).

fof(f102,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f101])).

fof(f495,plain,
    ( ! [X1] :
        ( ~ l1_struct_0(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1))
        | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2))
        | k2_struct_0(X1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(X1),sK2) )
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_33
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f494,f268])).

fof(f494,plain,
    ( ! [X1] :
        ( k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X1),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1))
        | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2))
        | ~ l1_struct_0(X1) )
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_33
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f493,f120])).

fof(f493,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1))
        | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2))
        | ~ l1_struct_0(X1)
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2) )
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_33
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f492,f268])).

fof(f492,plain,
    ( ! [X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1))
        | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2))
        | ~ l1_struct_0(X1)
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2) )
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_33
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f491,f120])).

fof(f491,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1))
        | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2))
        | ~ l1_struct_0(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2) )
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_33
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f490,f268])).

fof(f490,plain,
    ( ! [X1] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X1))
        | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2))
        | ~ l1_struct_0(X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2) )
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_33
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f489,f120])).

fof(f489,plain,
    ( ! [X1] :
        ( v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2))
        | ~ l1_struct_0(X1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2) )
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_33
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f488,f268])).

fof(f488,plain,
    ( ! [X1] :
        ( v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X1),sK2))
        | ~ l1_struct_0(X1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2) )
    | ~ spl3_9
    | ~ spl3_11
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f479,f120])).

fof(f479,plain,
    ( ! [X1] :
        ( v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),sK2))
        | ~ l1_struct_0(X1)
        | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2) )
    | ~ spl3_9
    | ~ spl3_53 ),
    inference(resolution,[],[f476,f110])).

fof(f110,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f109])).

fof(f476,plain,
    ( ! [X0,X1] :
        ( ~ l1_struct_0(X0)
        | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2))
        | ~ l1_struct_0(X1)
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) )
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f475])).

fof(f477,plain,
    ( ~ spl3_6
    | spl3_53
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f473,f81,f475,f97])).

fof(f473,plain,
    ( ! [X0,X1] :
        ( v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2))
        | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
        | ~ v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1))
        | ~ v1_funct_1(sK2)
        | ~ l1_struct_0(X1)
        | ~ l1_struct_0(X0) )
    | ~ spl3_2 ),
    inference(resolution,[],[f57,f82])).

fof(f82,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_2 ),
    inference(avatar_component_clause,[],[f81])).

fof(f57,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))
      | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
      | ~ v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
      | ~ v1_funct_1(X2)
      | ~ l1_struct_0(X1)
      | ~ l1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
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
    inference(flattening,[],[f21])).

% (10645)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f21,plain,(
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
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
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

fof(f472,plain,
    ( ~ spl3_52
    | spl3_38
    | ~ spl3_51 ),
    inference(avatar_split_clause,[],[f468,f456,f309,f470])).

fof(f309,plain,
    ( spl3_38
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f468,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)
    | spl3_38
    | ~ spl3_51 ),
    inference(superposition,[],[f310,f457])).

fof(f310,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)
    | spl3_38 ),
    inference(avatar_component_clause,[],[f309])).

fof(f458,plain,
    ( ~ spl3_39
    | spl3_51
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_50 ),
    inference(avatar_split_clause,[],[f454,f426,f267,f205,f119,f115,f89,f85,f456,f314])).

fof(f426,plain,
    ( spl3_50
  <=> ! [X1,X0] :
        ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f454,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_50 ),
    inference(trivial_inequality_removal,[],[f453])).

fof(f453,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_50 ),
    inference(forward_demodulation,[],[f452,f206])).

fof(f452,plain,
    ( k2_struct_0(sK1) != k2_relat_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_50 ),
    inference(forward_demodulation,[],[f451,f116])).

fof(f451,plain,
    ( u1_struct_0(sK1) != k2_relat_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_50 ),
    inference(forward_demodulation,[],[f450,f206])).

fof(f450,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_50 ),
    inference(forward_demodulation,[],[f449,f86])).

fof(f449,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_50 ),
    inference(forward_demodulation,[],[f448,f268])).

fof(f448,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_50 ),
    inference(forward_demodulation,[],[f447,f120])).

fof(f447,plain,
    ( k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_50 ),
    inference(forward_demodulation,[],[f446,f206])).

fof(f446,plain,
    ( k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_50 ),
    inference(forward_demodulation,[],[f445,f116])).

fof(f445,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_50 ),
    inference(forward_demodulation,[],[f444,f268])).

fof(f444,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_50 ),
    inference(forward_demodulation,[],[f443,f120])).

fof(f443,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_24
    | ~ spl3_50 ),
    inference(forward_demodulation,[],[f442,f206])).

fof(f442,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_50 ),
    inference(forward_demodulation,[],[f439,f116])).

% (10644)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
fof(f439,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_50 ),
    inference(resolution,[],[f427,f90])).

fof(f427,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | k2_relset_1(X0,X1,sK2) != X1 )
    | ~ spl3_50 ),
    inference(avatar_component_clause,[],[f426])).

fof(f435,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f434,plain,
    ( ~ spl3_43
    | ~ spl3_39
    | ~ spl3_36
    | ~ spl3_44
    | spl3_48 ),
    inference(avatar_split_clause,[],[f432,f409,f360,f285,f314,f339])).

fof(f360,plain,
    ( spl3_44
  <=> ! [X1,X0] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_2(k2_funct_1(sK2),X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f432,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_36
    | ~ spl3_44
    | spl3_48 ),
    inference(trivial_inequality_removal,[],[f431])).

fof(f431,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_36
    | ~ spl3_44
    | spl3_48 ),
    inference(forward_demodulation,[],[f430,f286])).

fof(f430,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_44
    | spl3_48 ),
    inference(resolution,[],[f410,f361])).

fof(f361,plain,
    ( ! [X0,X1] :
        ( v1_funct_2(k2_funct_1(sK2),X1,X0)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1 )
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f360])).

fof(f410,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | spl3_48 ),
    inference(avatar_component_clause,[],[f409])).

fof(f428,plain,
    ( ~ spl3_6
    | spl3_50
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f424,f81,f426,f97])).

fof(f424,plain,
    ( ! [X0,X1] :
        ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | k2_relset_1(X0,X1,sK2) != X1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_2 ),
    inference(resolution,[],[f73,f82])).

fof(f417,plain,
    ( spl3_49
    | ~ spl3_19
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f413,f389,f178,f415])).

fof(f178,plain,
    ( spl3_19
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f413,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_19
    | ~ spl3_46 ),
    inference(forward_demodulation,[],[f403,f179])).

fof(f179,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f178])).

fof(f403,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_46 ),
    inference(resolution,[],[f390,f68])).

fof(f68,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f391,plain,
    ( ~ spl3_39
    | spl3_46
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_45 ),
    inference(avatar_split_clause,[],[f386,f368,f267,f205,f119,f115,f89,f85,f389,f314])).

fof(f368,plain,
    ( spl3_45
  <=> ! [X1,X0] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f386,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f385,f206])).

fof(f385,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f384,f116])).

fof(f384,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f383,f268])).

fof(f383,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK0))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f382,f120])).

fof(f382,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_45 ),
    inference(trivial_inequality_removal,[],[f381])).

fof(f381,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f380,f206])).

fof(f380,plain,
    ( k2_struct_0(sK1) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f379,f116])).

fof(f379,plain,
    ( u1_struct_0(sK1) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f378,f206])).

fof(f378,plain,
    ( u1_struct_0(sK1) != k2_struct_0(sK1)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl3_3
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f377,f86])).

fof(f377,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_33
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f376,f268])).

fof(f376,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | ~ spl3_24
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f375,f120])).

fof(f375,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_24
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f374,f206])).

fof(f374,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f371,f116])).

fof(f371,plain,
    ( ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0))))
    | ~ spl3_4
    | ~ spl3_45 ),
    inference(resolution,[],[f369,f90])).

fof(f369,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_relset_1(X0,X1,sK2) != X1
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f368])).

fof(f370,plain,
    ( ~ spl3_6
    | spl3_45
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f366,f81,f368,f97])).

fof(f366,plain,
    ( ! [X0,X1] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_2 ),
    inference(resolution,[],[f72,f82])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
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

fof(f362,plain,
    ( ~ spl3_6
    | spl3_44
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f358,f81,f360,f97])).

fof(f358,plain,
    ( ! [X0,X1] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | v1_funct_2(k2_funct_1(sK2),X1,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_2 ),
    inference(resolution,[],[f71,f82])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f341,plain,
    ( spl3_43
    | ~ spl3_28
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f336,f267,f229,f339])).

fof(f229,plain,
    ( spl3_28
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f336,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_28
    | ~ spl3_33 ),
    inference(superposition,[],[f230,f268])).

fof(f230,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f229])).

fof(f319,plain,
    ( spl3_39
    | ~ spl3_29
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f303,f267,f233,f314])).

fof(f233,plain,
    ( spl3_29
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f303,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_29
    | ~ spl3_33 ),
    inference(superposition,[],[f234,f268])).

fof(f234,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f233])).

fof(f311,plain,
    ( ~ spl3_38
    | spl3_13
    | ~ spl3_24
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f307,f267,f205,f131,f309])).

fof(f131,plain,
    ( spl3_13
  <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f307,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)
    | spl3_13
    | ~ spl3_24
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f299,f206])).

fof(f299,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),sK2)
    | spl3_13
    | ~ spl3_33 ),
    inference(superposition,[],[f132,f268])).

fof(f132,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | spl3_13 ),
    inference(avatar_component_clause,[],[f131])).

fof(f296,plain,
    ( spl3_28
    | ~ spl3_14
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f295,f205,f138,f229])).

fof(f138,plain,
    ( spl3_14
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f295,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_14
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f139,f206])).

fof(f139,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f138])).

fof(f282,plain,
    ( ~ spl3_14
    | spl3_32 ),
    inference(avatar_contradiction_clause,[],[f280])).

fof(f280,plain,
    ( $false
    | ~ spl3_14
    | spl3_32 ),
    inference(subsumption_resolution,[],[f139,f279])).

fof(f279,plain,
    ( ! [X0] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))
    | spl3_32 ),
    inference(resolution,[],[f265,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f5])).

% (10658)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f265,plain,
    ( ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | spl3_32 ),
    inference(avatar_component_clause,[],[f264])).

fof(f264,plain,
    ( spl3_32
  <=> v4_relat_1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f277,plain,
    ( ~ spl3_6
    | spl3_34
    | spl3_35
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f270,f81,f275,f272,f97])).

fof(f270,plain,
    ( ! [X0,X1] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | v1_funct_1(k2_funct_1(sK2))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_2 ),
    inference(resolution,[],[f70,f82])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f37])).

fof(f269,plain,
    ( ~ spl3_16
    | ~ spl3_32
    | spl3_33
    | ~ spl3_31 ),
    inference(avatar_split_clause,[],[f262,f258,f267,f264,f156])).

fof(f258,plain,
    ( spl3_31
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f262,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v4_relat_1(sK2,k2_struct_0(sK0))
    | ~ v1_relat_1(sK2)
    | ~ spl3_31 ),
    inference(resolution,[],[f259,f66])).

fof(f66,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f8])).

% (10659)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f8,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f259,plain,
    ( v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f258])).

fof(f261,plain,
    ( spl3_31
    | ~ spl3_29
    | ~ spl3_6
    | ~ spl3_28
    | spl3_30 ),
    inference(avatar_split_clause,[],[f256,f239,f229,f97,f233,f258])).

fof(f239,plain,
    ( spl3_30
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f256,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_6
    | ~ spl3_28
    | spl3_30 ),
    inference(resolution,[],[f255,f230])).

fof(f255,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK2))))
        | ~ v1_funct_2(sK2,X0,k2_relat_1(sK2))
        | v1_partfun1(sK2,X0) )
    | ~ spl3_6
    | spl3_30 ),
    inference(resolution,[],[f243,f98])).

fof(f98,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f97])).

fof(f243,plain,
    ( ! [X0,X1] :
        ( ~ v1_funct_1(X0)
        | ~ v1_funct_2(X0,X1,k2_relat_1(sK2))
        | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(sK2))))
        | v1_partfun1(X0,X1) )
    | spl3_30 ),
    inference(resolution,[],[f240,f65])).

fof(f65,plain,(
    ! [X2,X0,X1] :
      ( v1_xboole_0(X1)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_partfun1(X2,X0) ) ),
    inference(cnf_transformation,[],[f31])).

fof(f31,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f30])).

fof(f30,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

fof(f240,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_30 ),
    inference(avatar_component_clause,[],[f239])).

fof(f241,plain,
    ( spl3_8
    | ~ spl3_7
    | ~ spl3_30
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f223,f205,f239,f101,f105])).

fof(f105,plain,
    ( spl3_8
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f223,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_24 ),
    inference(superposition,[],[f59,f206])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(k2_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).

fof(f235,plain,
    ( spl3_29
    | ~ spl3_15
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f222,f205,f143,f233])).

fof(f143,plain,
    ( spl3_15
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f222,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_15
    | ~ spl3_24 ),
    inference(superposition,[],[f144,f206])).

fof(f144,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f143])).

fof(f216,plain,
    ( spl3_24
    | ~ spl3_12
    | ~ spl3_23 ),
    inference(avatar_split_clause,[],[f214,f200,f123,f205])).

fof(f123,plain,
    ( spl3_12
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f200,plain,
    ( spl3_23
  <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f214,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_12
    | ~ spl3_23 ),
    inference(superposition,[],[f124,f201])).

fof(f201,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_23 ),
    inference(avatar_component_clause,[],[f200])).

fof(f124,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f123])).

fof(f202,plain,
    ( spl3_23
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f198,f119,f115,f89,f200])).

fof(f198,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f197,f120])).

fof(f197,plain,
    ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f195,f116])).

fof(f195,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f68,f90])).

fof(f180,plain,
    ( ~ spl3_16
    | ~ spl3_6
    | spl3_19
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f163,f81,f178,f97,f156])).

fof(f163,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_2 ),
    inference(resolution,[],[f62,f82])).

fof(f62,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
          & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f176,plain,(
    spl3_18 ),
    inference(avatar_contradiction_clause,[],[f174])).

fof(f174,plain,
    ( $false
    | spl3_18 ),
    inference(resolution,[],[f171,f63])).

fof(f63,plain,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    inference(cnf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).

fof(f171,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | spl3_18 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl3_18
  <=> v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f172,plain,
    ( ~ spl3_18
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | spl3_16 ),
    inference(avatar_split_clause,[],[f168,f156,f119,f115,f89,f170])).

fof(f168,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11
    | spl3_16 ),
    inference(forward_demodulation,[],[f167,f120])).

fof(f167,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))
    | ~ spl3_4
    | ~ spl3_10
    | spl3_16 ),
    inference(forward_demodulation,[],[f165,f116])).

fof(f165,plain,
    ( ~ v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))
    | ~ spl3_4
    | spl3_16 ),
    inference(resolution,[],[f164,f90])).

fof(f164,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(X0))
        | ~ v1_relat_1(X0) )
    | spl3_16 ),
    inference(resolution,[],[f157,f58])).

fof(f58,plain,(
    ! [X0,X1] :
      ( v1_relat_1(X1)
      | ~ m1_subset_1(X1,k1_zfmisc_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
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

fof(f157,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_16 ),
    inference(avatar_component_clause,[],[f156])).

fof(f145,plain,
    ( spl3_15
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f141,f119,f115,f93,f143])).

fof(f93,plain,
    ( spl3_5
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f141,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f128,f120])).

fof(f128,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_5
    | ~ spl3_10 ),
    inference(superposition,[],[f94,f116])).

fof(f94,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f93])).

fof(f140,plain,
    ( spl3_14
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f136,f119,f115,f89,f138])).

fof(f136,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f127,f120])).

fof(f127,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_4
    | ~ spl3_10 ),
    inference(superposition,[],[f90,f116])).

fof(f135,plain,
    ( spl3_12
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f134,f119,f115,f85,f123])).

fof(f134,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_3
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f126,f120])).

fof(f126,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(superposition,[],[f86,f116])).

fof(f133,plain,
    ( ~ spl3_13
    | spl3_1
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f129,f119,f115,f77,f131])).

fof(f77,plain,
    ( spl3_1
  <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f129,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | spl3_1
    | ~ spl3_10
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f125,f120])).

fof(f125,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)
    | spl3_1
    | ~ spl3_10 ),
    inference(superposition,[],[f78,f116])).

fof(f78,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f77])).

fof(f121,plain,
    ( spl3_11
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f113,f109,f119])).

fof(f113,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_9 ),
    inference(resolution,[],[f56,f110])).

fof(f56,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f117,plain,
    ( spl3_10
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f112,f101,f115])).

fof(f112,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_7 ),
    inference(resolution,[],[f56,f102])).

fof(f111,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f47,f109])).

fof(f47,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f44,f43,f42])).

fof(f42,plain,
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

fof(f43,plain,
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

fof(f44,plain,
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

fof(f19,plain,(
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
    inference(flattening,[],[f18])).

fof(f18,plain,(
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
    inference(ennf_transformation,[],[f16])).

% (10653)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f16,negated_conjecture,(
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
    inference(negated_conjecture,[],[f15])).

fof(f15,conjecture,(
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

fof(f107,plain,(
    ~ spl3_8 ),
    inference(avatar_split_clause,[],[f48,f105])).

fof(f48,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f103,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f49,f101])).

fof(f49,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f45])).

fof(f99,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f50,f97])).

fof(f50,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f95,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f51,f93])).

fof(f51,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f45])).

fof(f91,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f52,f89])).

fof(f52,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f45])).

fof(f87,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f53,f85])).

fof(f53,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f83,plain,(
    spl3_2 ),
    inference(avatar_split_clause,[],[f54,f81])).

fof(f54,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f45])).

fof(f79,plain,(
    ~ spl3_1 ),
    inference(avatar_split_clause,[],[f55,f77])).

fof(f55,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f45])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n010.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 16:34:14 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.47  % (10647)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (10651)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.48  % (10647)Refutation found. Thanks to Tanya!
% 0.21/0.48  % SZS status Theorem for theBenchmark
% 0.21/0.48  % (10654)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.21/0.48  % (10643)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (10652)lrs+10_50_add=large:afp=40000:afq=1.2:amm=sco:anc=none:br=off:cond=on:fsr=off:gsp=input_only:gs=on:irw=on:lma=on:nm=64:nwc=1:stl=30:sos=all:sp=reverse_arity:urr=on_21 on theBenchmark
% 0.21/0.49  % (10656)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.49  % (10646)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.49  % (10648)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.21/0.49  % (10641)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f721,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f79,f83,f87,f91,f95,f99,f103,f107,f111,f117,f121,f133,f135,f140,f145,f172,f176,f180,f202,f216,f235,f241,f261,f269,f277,f282,f296,f311,f319,f341,f362,f370,f391,f417,f428,f434,f435,f458,f472,f477,f556,f617,f655,f698,f703,f708,f713,f717])).
% 0.21/0.50  fof(f717,plain,(
% 0.21/0.50    ~spl3_39 | ~spl3_6 | ~spl3_43 | ~spl3_85),
% 0.21/0.50    inference(avatar_split_clause,[],[f715,f711,f339,f97,f314])).
% 0.21/0.50  fof(f314,plain,(
% 0.21/0.50    spl3_39 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.21/0.50  fof(f97,plain,(
% 0.21/0.50    spl3_6 <=> v1_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.50  fof(f339,plain,(
% 0.21/0.50    spl3_43 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.21/0.50  fof(f711,plain,(
% 0.21/0.50    spl3_85 <=> ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_85])])).
% 0.21/0.50  fof(f715,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_43 | ~spl3_85)),
% 0.21/0.50    inference(resolution,[],[f712,f340])).
% 0.21/0.50  fof(f340,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_43),
% 0.21/0.50    inference(avatar_component_clause,[],[f339])).
% 0.21/0.50  fof(f712,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_1(X0) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2))) ) | ~spl3_85),
% 0.21/0.50    inference(avatar_component_clause,[],[f711])).
% 0.21/0.50  fof(f713,plain,(
% 0.21/0.50    ~spl3_6 | ~spl3_39 | ~spl3_43 | spl3_85 | spl3_84),
% 0.21/0.50    inference(avatar_split_clause,[],[f709,f706,f711,f339,f314,f97])).
% 0.21/0.50  fof(f706,plain,(
% 0.21/0.50    spl3_84 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).
% 0.21/0.50  fof(f709,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(X0,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2)) ) | spl3_84),
% 0.21/0.50    inference(resolution,[],[f707,f74])).
% 0.21/0.50  fof(f74,plain,(
% 0.21/0.50    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f41])).
% 0.21/0.50  fof(f41,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f40])).
% 0.21/0.50  fof(f40,plain,(
% 0.21/0.50    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f9])).
% 0.21/0.50  fof(f9,axiom,(
% 0.21/0.50    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 0.21/0.50  fof(f707,plain,(
% 0.21/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | spl3_84),
% 0.21/0.50    inference(avatar_component_clause,[],[f706])).
% 0.21/0.50  fof(f708,plain,(
% 0.21/0.50    ~spl3_16 | ~spl3_6 | ~spl3_2 | ~spl3_84 | spl3_83),
% 0.21/0.50    inference(avatar_split_clause,[],[f704,f701,f706,f81,f97,f156])).
% 0.21/0.50  fof(f156,plain,(
% 0.21/0.50    spl3_16 <=> v1_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.50  fof(f81,plain,(
% 0.21/0.50    spl3_2 <=> v2_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.50  fof(f701,plain,(
% 0.21/0.50    spl3_83 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).
% 0.21/0.50  fof(f704,plain,(
% 0.21/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_83),
% 0.21/0.50    inference(superposition,[],[f702,f60])).
% 0.21/0.50  fof(f60,plain,(
% 0.21/0.50    ( ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f27])).
% 0.21/0.50  fof(f27,plain,(
% 0.21/0.50    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f26])).
% 0.21/0.50  fof(f26,plain,(
% 0.21/0.50    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f4])).
% 0.21/0.50  fof(f4,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.21/0.50  fof(f702,plain,(
% 0.21/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2) | spl3_83),
% 0.21/0.50    inference(avatar_component_clause,[],[f701])).
% 0.21/0.50  fof(f703,plain,(
% 0.21/0.50    ~spl3_83 | spl3_52 | ~spl3_82),
% 0.21/0.50    inference(avatar_split_clause,[],[f699,f696,f470,f701])).
% 0.21/0.50  fof(f470,plain,(
% 0.21/0.50    spl3_52 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.21/0.50  fof(f696,plain,(
% 0.21/0.50    spl3_82 <=> k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).
% 0.21/0.50  fof(f699,plain,(
% 0.21/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_funct_1(k2_funct_1(sK2)),sK2) | (spl3_52 | ~spl3_82)),
% 0.21/0.50    inference(superposition,[],[f471,f697])).
% 0.21/0.50  fof(f697,plain,(
% 0.21/0.50    k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2)) | ~spl3_82),
% 0.21/0.50    inference(avatar_component_clause,[],[f696])).
% 0.21/0.50  fof(f471,plain,(
% 0.21/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) | spl3_52),
% 0.21/0.50    inference(avatar_component_clause,[],[f470])).
% 0.21/0.50  fof(f698,plain,(
% 0.21/0.50    spl3_82 | ~spl3_48 | ~spl3_46 | ~spl3_49 | ~spl3_74),
% 0.21/0.50    inference(avatar_split_clause,[],[f694,f615,f415,f389,f409,f696])).
% 0.21/0.50  fof(f409,plain,(
% 0.21/0.50    spl3_48 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_48])])).
% 0.21/0.50  fof(f389,plain,(
% 0.21/0.50    spl3_46 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.21/0.50  fof(f415,plain,(
% 0.21/0.50    spl3_49 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.21/0.50  fof(f615,plain,(
% 0.21/0.50    spl3_74 <=> ! [X9,X8] : (k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X8,X9,k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),X8,X9) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | k2_relset_1(X8,X9,k2_funct_1(sK2)) != X9)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).
% 0.21/0.50  fof(f694,plain,(
% 0.21/0.50    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2)) | (~spl3_46 | ~spl3_49 | ~spl3_74)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f693])).
% 0.21/0.50  fof(f693,plain,(
% 0.21/0.50    k1_relat_1(sK2) != k1_relat_1(sK2) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2)) | (~spl3_46 | ~spl3_49 | ~spl3_74)),
% 0.21/0.50    inference(forward_demodulation,[],[f692,f416])).
% 0.21/0.50  fof(f416,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_49),
% 0.21/0.50    inference(avatar_component_clause,[],[f415])).
% 0.21/0.50  fof(f692,plain,(
% 0.21/0.50    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k2_funct_1(k2_funct_1(sK2)) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_46 | ~spl3_74)),
% 0.21/0.50    inference(resolution,[],[f616,f390])).
% 0.21/0.50  fof(f390,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_46),
% 0.21/0.50    inference(avatar_component_clause,[],[f389])).
% 0.21/0.50  fof(f616,plain,(
% 0.21/0.50    ( ! [X8,X9] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_2(k2_funct_1(sK2),X8,X9) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X8,X9,k2_funct_1(sK2)) | k2_relset_1(X8,X9,k2_funct_1(sK2)) != X9) ) | ~spl3_74),
% 0.21/0.50    inference(avatar_component_clause,[],[f615])).
% 0.21/0.50  fof(f655,plain,(
% 0.21/0.50    ~spl3_39 | ~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_35),
% 0.21/0.50    inference(avatar_split_clause,[],[f654,f275,f267,f205,f119,f115,f89,f85,f314])).
% 0.21/0.50  fof(f85,plain,(
% 0.21/0.50    spl3_3 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.50  fof(f89,plain,(
% 0.21/0.50    spl3_4 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.50  fof(f115,plain,(
% 0.21/0.50    spl3_10 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.50  fof(f119,plain,(
% 0.21/0.50    spl3_11 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.50  fof(f205,plain,(
% 0.21/0.50    spl3_24 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.50  fof(f267,plain,(
% 0.21/0.50    spl3_33 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.50  fof(f275,plain,(
% 0.21/0.50    spl3_35 <=> ! [X1,X0] : (k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.21/0.50  fof(f654,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_35)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f653])).
% 0.21/0.50  fof(f653,plain,(
% 0.21/0.50    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_35)),
% 0.21/0.50    inference(forward_demodulation,[],[f652,f206])).
% 0.21/0.50  fof(f206,plain,(
% 0.21/0.50    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_24),
% 0.21/0.50    inference(avatar_component_clause,[],[f205])).
% 0.21/0.50  fof(f652,plain,(
% 0.21/0.50    k2_struct_0(sK1) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_35)),
% 0.21/0.50    inference(forward_demodulation,[],[f651,f116])).
% 0.21/0.50  fof(f116,plain,(
% 0.21/0.50    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_10),
% 0.21/0.50    inference(avatar_component_clause,[],[f115])).
% 0.21/0.50  fof(f651,plain,(
% 0.21/0.50    u1_struct_0(sK1) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_35)),
% 0.21/0.50    inference(forward_demodulation,[],[f650,f206])).
% 0.21/0.50  fof(f650,plain,(
% 0.21/0.50    u1_struct_0(sK1) != k2_struct_0(sK1) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_35)),
% 0.21/0.50    inference(forward_demodulation,[],[f649,f86])).
% 0.21/0.50  fof(f86,plain,(
% 0.21/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_3),
% 0.21/0.50    inference(avatar_component_clause,[],[f85])).
% 0.21/0.50  fof(f649,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_35)),
% 0.21/0.50    inference(forward_demodulation,[],[f648,f268])).
% 0.21/0.50  fof(f268,plain,(
% 0.21/0.50    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_33),
% 0.21/0.50    inference(avatar_component_clause,[],[f267])).
% 0.21/0.50  fof(f648,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_35)),
% 0.21/0.50    inference(forward_demodulation,[],[f647,f120])).
% 0.21/0.50  fof(f120,plain,(
% 0.21/0.50    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_11),
% 0.21/0.50    inference(avatar_component_clause,[],[f119])).
% 0.21/0.50  fof(f647,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_10 | ~spl3_24 | ~spl3_35)),
% 0.21/0.50    inference(forward_demodulation,[],[f646,f206])).
% 0.21/0.50  fof(f646,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_10 | ~spl3_35)),
% 0.21/0.50    inference(forward_demodulation,[],[f643,f116])).
% 0.21/0.50  fof(f643,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_35)),
% 0.21/0.50    inference(resolution,[],[f276,f90])).
% 0.21/0.50  fof(f90,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f89])).
% 0.21/0.50  fof(f276,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_relset_1(X0,X1,sK2) != X1) ) | ~spl3_35),
% 0.21/0.50    inference(avatar_component_clause,[],[f275])).
% 0.21/0.50  fof(f617,plain,(
% 0.21/0.50    ~spl3_34 | spl3_74 | ~spl3_62),
% 0.21/0.50    inference(avatar_split_clause,[],[f584,f554,f615,f272])).
% 0.21/0.50  fof(f272,plain,(
% 0.21/0.50    spl3_34 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_34])])).
% 0.21/0.50  fof(f554,plain,(
% 0.21/0.50    spl3_62 <=> v2_funct_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_62])])).
% 0.21/0.50  fof(f584,plain,(
% 0.21/0.50    ( ! [X8,X9] : (k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X8,X9,k2_funct_1(sK2)) | k2_relset_1(X8,X9,k2_funct_1(sK2)) != X9 | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X8,X9))) | ~v1_funct_2(k2_funct_1(sK2),X8,X9) | ~v1_funct_1(k2_funct_1(sK2))) ) | ~spl3_62),
% 0.21/0.50    inference(resolution,[],[f555,f73])).
% 0.21/0.50  fof(f73,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f39])).
% 0.21/0.50  fof(f39,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f38])).
% 0.21/0.50  fof(f38,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.21/0.50  fof(f555,plain,(
% 0.21/0.50    v2_funct_1(k2_funct_1(sK2)) | ~spl3_62),
% 0.21/0.50    inference(avatar_component_clause,[],[f554])).
% 0.21/0.50  fof(f556,plain,(
% 0.21/0.50    ~spl3_43 | ~spl3_39 | spl3_62 | ~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_36 | ~spl3_51 | ~spl3_53),
% 0.21/0.50    inference(avatar_split_clause,[],[f552,f475,f456,f285,f267,f205,f119,f115,f109,f101,f554,f314,f339])).
% 0.21/0.50  fof(f101,plain,(
% 0.21/0.50    spl3_7 <=> l1_struct_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.50  fof(f109,plain,(
% 0.21/0.50    spl3_9 <=> l1_struct_0(sK0)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.50  fof(f285,plain,(
% 0.21/0.50    spl3_36 <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_36])])).
% 0.21/0.50  fof(f456,plain,(
% 0.21/0.50    spl3_51 <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 0.21/0.50  fof(f475,plain,(
% 0.21/0.50    spl3_53 <=> ! [X1,X0] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) | ~l1_struct_0(X0) | ~l1_struct_0(X1) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 0.21/0.50  fof(f552,plain,(
% 0.21/0.50    v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_36 | ~spl3_51 | ~spl3_53)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f551])).
% 0.21/0.50  fof(f551,plain,(
% 0.21/0.50    k2_relat_1(sK2) != k2_relat_1(sK2) | v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_36 | ~spl3_51 | ~spl3_53)),
% 0.21/0.50    inference(forward_demodulation,[],[f550,f286])).
% 0.21/0.50  fof(f286,plain,(
% 0.21/0.50    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_36),
% 0.21/0.50    inference(avatar_component_clause,[],[f285])).
% 0.21/0.50  fof(f550,plain,(
% 0.21/0.50    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_51 | ~spl3_53)),
% 0.21/0.50    inference(forward_demodulation,[],[f549,f206])).
% 0.21/0.50  fof(f549,plain,(
% 0.21/0.50    k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),k2_struct_0(sK1),sK2) | v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_51 | ~spl3_53)),
% 0.21/0.50    inference(forward_demodulation,[],[f548,f116])).
% 0.21/0.50  fof(f548,plain,(
% 0.21/0.50    v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) | (~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_51 | ~spl3_53)),
% 0.21/0.50    inference(forward_demodulation,[],[f547,f457])).
% 0.21/0.50  fof(f457,plain,(
% 0.21/0.50    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_51),
% 0.21/0.50    inference(avatar_component_clause,[],[f456])).
% 0.21/0.50  fof(f547,plain,(
% 0.21/0.50    v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) | (~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_53)),
% 0.21/0.50    inference(forward_demodulation,[],[f546,f206])).
% 0.21/0.50  fof(f546,plain,(
% 0.21/0.50    v2_funct_1(k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) | (~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_53)),
% 0.21/0.50    inference(forward_demodulation,[],[f545,f116])).
% 0.21/0.50  fof(f545,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) | (~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_53)),
% 0.21/0.50    inference(forward_demodulation,[],[f544,f206])).
% 0.21/0.50  fof(f544,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_struct_0(sK1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) | (~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_53)),
% 0.21/0.50    inference(forward_demodulation,[],[f543,f116])).
% 0.21/0.50  fof(f543,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) | (~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_53)),
% 0.21/0.50    inference(forward_demodulation,[],[f542,f206])).
% 0.21/0.50  fof(f542,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) | (~spl3_7 | ~spl3_9 | ~spl3_10 | ~spl3_11 | ~spl3_33 | ~spl3_53)),
% 0.21/0.50    inference(forward_demodulation,[],[f540,f116])).
% 0.21/0.50  fof(f540,plain,(
% 0.21/0.50    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(sK1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(sK1)) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(sK1),sK2) | (~spl3_7 | ~spl3_9 | ~spl3_11 | ~spl3_33 | ~spl3_53)),
% 0.21/0.50    inference(resolution,[],[f495,f102])).
% 0.21/0.50  fof(f102,plain,(
% 0.21/0.50    l1_struct_0(sK1) | ~spl3_7),
% 0.21/0.50    inference(avatar_component_clause,[],[f101])).
% 0.21/0.50  fof(f495,plain,(
% 0.21/0.50    ( ! [X1] : (~l1_struct_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1)) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2)) | k2_struct_0(X1) != k2_relset_1(k1_relat_1(sK2),u1_struct_0(X1),sK2)) ) | (~spl3_9 | ~spl3_11 | ~spl3_33 | ~spl3_53)),
% 0.21/0.50    inference(forward_demodulation,[],[f494,f268])).
% 0.21/0.50  fof(f494,plain,(
% 0.21/0.50    ( ! [X1] : (k2_struct_0(X1) != k2_relset_1(k2_struct_0(sK0),u1_struct_0(X1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1)) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2)) | ~l1_struct_0(X1)) ) | (~spl3_9 | ~spl3_11 | ~spl3_33 | ~spl3_53)),
% 0.21/0.50    inference(forward_demodulation,[],[f493,f120])).
% 0.21/0.50  fof(f493,plain,(
% 0.21/0.50    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),u1_struct_0(X1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1)) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2)) | ~l1_struct_0(X1) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2)) ) | (~spl3_9 | ~spl3_11 | ~spl3_33 | ~spl3_53)),
% 0.21/0.50    inference(forward_demodulation,[],[f492,f268])).
% 0.21/0.50  fof(f492,plain,(
% 0.21/0.50    ( ! [X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1)) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2)) | ~l1_struct_0(X1) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2)) ) | (~spl3_9 | ~spl3_11 | ~spl3_33 | ~spl3_53)),
% 0.21/0.50    inference(forward_demodulation,[],[f491,f120])).
% 0.21/0.50  fof(f491,plain,(
% 0.21/0.50    ( ! [X1] : (~v1_funct_2(sK2,k1_relat_1(sK2),u1_struct_0(X1)) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2)) | ~l1_struct_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2)) ) | (~spl3_9 | ~spl3_11 | ~spl3_33 | ~spl3_53)),
% 0.21/0.50    inference(forward_demodulation,[],[f490,f268])).
% 0.21/0.50  fof(f490,plain,(
% 0.21/0.50    ( ! [X1] : (~v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(X1)) | v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2)) | ~l1_struct_0(X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2)) ) | (~spl3_9 | ~spl3_11 | ~spl3_33 | ~spl3_53)),
% 0.21/0.50    inference(forward_demodulation,[],[f489,f120])).
% 0.21/0.50  fof(f489,plain,(
% 0.21/0.50    ( ! [X1] : (v2_funct_1(k2_tops_2(k1_relat_1(sK2),u1_struct_0(X1),sK2)) | ~l1_struct_0(X1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2)) ) | (~spl3_9 | ~spl3_11 | ~spl3_33 | ~spl3_53)),
% 0.21/0.50    inference(forward_demodulation,[],[f488,f268])).
% 0.21/0.50  fof(f488,plain,(
% 0.21/0.50    ( ! [X1] : (v2_funct_1(k2_tops_2(k2_struct_0(sK0),u1_struct_0(X1),sK2)) | ~l1_struct_0(X1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2)) ) | (~spl3_9 | ~spl3_11 | ~spl3_53)),
% 0.21/0.50    inference(forward_demodulation,[],[f479,f120])).
% 0.21/0.50  fof(f479,plain,(
% 0.21/0.50    ( ! [X1] : (v2_funct_1(k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),sK2)) | ~l1_struct_0(X1) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),sK2)) ) | (~spl3_9 | ~spl3_53)),
% 0.21/0.50    inference(resolution,[],[f476,f110])).
% 0.21/0.50  fof(f110,plain,(
% 0.21/0.50    l1_struct_0(sK0) | ~spl3_9),
% 0.21/0.50    inference(avatar_component_clause,[],[f109])).
% 0.21/0.50  fof(f476,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~l1_struct_0(X0) | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) | ~l1_struct_0(X1) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2)) ) | ~spl3_53),
% 0.21/0.50    inference(avatar_component_clause,[],[f475])).
% 0.21/0.50  fof(f477,plain,(
% 0.21/0.50    ~spl3_6 | spl3_53 | ~spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f473,f81,f475,f97])).
% 0.21/0.50  fof(f473,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),sK2)) | k2_struct_0(X1) != k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(sK2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(sK2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) ) | ~spl3_2),
% 0.21/0.50    inference(resolution,[],[f57,f82])).
% 0.21/0.50  fof(f82,plain,(
% 0.21/0.50    v2_funct_1(sK2) | ~spl3_2),
% 0.21/0.50    inference(avatar_component_clause,[],[f81])).
% 0.21/0.50  fof(f57,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2) | ~l1_struct_0(X1) | ~l1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : (v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | ~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2)) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  % (10645)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (! [X2] : ((v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | (~v2_funct_1(X2) | k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) != k2_struct_0(X1))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) | ~v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) | ~v1_funct_1(X2))) | ~l1_struct_0(X1)) | ~l1_struct_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f14])).
% 0.21/0.50  fof(f14,axiom,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => v2_funct_1(k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_tops_2)).
% 0.21/0.50  fof(f472,plain,(
% 0.21/0.50    ~spl3_52 | spl3_38 | ~spl3_51),
% 0.21/0.50    inference(avatar_split_clause,[],[f468,f456,f309,f470])).
% 0.21/0.50  fof(f309,plain,(
% 0.21/0.50    spl3_38 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.21/0.50  fof(f468,plain,(
% 0.21/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) | (spl3_38 | ~spl3_51)),
% 0.21/0.50    inference(superposition,[],[f310,f457])).
% 0.21/0.50  fof(f310,plain,(
% 0.21/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) | spl3_38),
% 0.21/0.50    inference(avatar_component_clause,[],[f309])).
% 0.21/0.50  fof(f458,plain,(
% 0.21/0.50    ~spl3_39 | spl3_51 | ~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_50),
% 0.21/0.50    inference(avatar_split_clause,[],[f454,f426,f267,f205,f119,f115,f89,f85,f456,f314])).
% 0.21/0.50  fof(f426,plain,(
% 0.21/0.50    spl3_50 <=> ! [X1,X0] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.21/0.50  fof(f454,plain,(
% 0.21/0.50    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_50)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f453])).
% 0.21/0.50  fof(f453,plain,(
% 0.21/0.50    k2_relat_1(sK2) != k2_relat_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_50)),
% 0.21/0.50    inference(forward_demodulation,[],[f452,f206])).
% 0.21/0.50  fof(f452,plain,(
% 0.21/0.50    k2_struct_0(sK1) != k2_relat_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_50)),
% 0.21/0.50    inference(forward_demodulation,[],[f451,f116])).
% 0.21/0.50  fof(f451,plain,(
% 0.21/0.50    u1_struct_0(sK1) != k2_relat_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_50)),
% 0.21/0.50    inference(forward_demodulation,[],[f450,f206])).
% 0.21/0.50  fof(f450,plain,(
% 0.21/0.50    u1_struct_0(sK1) != k2_struct_0(sK1) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_50)),
% 0.21/0.50    inference(forward_demodulation,[],[f449,f86])).
% 0.21/0.50  fof(f449,plain,(
% 0.21/0.50    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_50)),
% 0.21/0.50    inference(forward_demodulation,[],[f448,f268])).
% 0.21/0.50  fof(f448,plain,(
% 0.21/0.50    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_50)),
% 0.21/0.50    inference(forward_demodulation,[],[f447,f120])).
% 0.21/0.50  fof(f447,plain,(
% 0.21/0.50    k2_funct_1(sK2) = k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_50)),
% 0.21/0.50    inference(forward_demodulation,[],[f446,f206])).
% 0.21/0.50  fof(f446,plain,(
% 0.21/0.50    k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_50)),
% 0.21/0.50    inference(forward_demodulation,[],[f445,f116])).
% 0.21/0.50  fof(f445,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_50)),
% 0.21/0.50    inference(forward_demodulation,[],[f444,f268])).
% 0.21/0.50  fof(f444,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_50)),
% 0.21/0.50    inference(forward_demodulation,[],[f443,f120])).
% 0.21/0.50  fof(f443,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_10 | ~spl3_24 | ~spl3_50)),
% 0.21/0.50    inference(forward_demodulation,[],[f442,f206])).
% 0.21/0.50  fof(f442,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_10 | ~spl3_50)),
% 0.21/0.50    inference(forward_demodulation,[],[f439,f116])).
% 0.21/0.50  % (10644)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.21/0.50  fof(f439,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_funct_1(sK2) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_50)),
% 0.21/0.50    inference(resolution,[],[f427,f90])).
% 0.21/0.50  fof(f427,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1) ) | ~spl3_50),
% 0.21/0.50    inference(avatar_component_clause,[],[f426])).
% 0.21/0.50  fof(f435,plain,(
% 0.21/0.50    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_struct_0(sK0) != k1_relat_1(sK2) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.21/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.50  fof(f434,plain,(
% 0.21/0.50    ~spl3_43 | ~spl3_39 | ~spl3_36 | ~spl3_44 | spl3_48),
% 0.21/0.50    inference(avatar_split_clause,[],[f432,f409,f360,f285,f314,f339])).
% 0.21/0.50  fof(f360,plain,(
% 0.21/0.50    spl3_44 <=> ! [X1,X0] : (k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(k2_funct_1(sK2),X1,X0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.21/0.50  fof(f432,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_36 | ~spl3_44 | spl3_48)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f431])).
% 0.21/0.50  fof(f431,plain,(
% 0.21/0.50    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_36 | ~spl3_44 | spl3_48)),
% 0.21/0.50    inference(forward_demodulation,[],[f430,f286])).
% 0.21/0.50  fof(f430,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_44 | spl3_48)),
% 0.21/0.50    inference(resolution,[],[f410,f361])).
% 0.21/0.50  fof(f361,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_funct_2(k2_funct_1(sK2),X1,X0) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1) ) | ~spl3_44),
% 0.21/0.50    inference(avatar_component_clause,[],[f360])).
% 0.21/0.50  fof(f410,plain,(
% 0.21/0.50    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | spl3_48),
% 0.21/0.50    inference(avatar_component_clause,[],[f409])).
% 0.21/0.50  fof(f428,plain,(
% 0.21/0.50    ~spl3_6 | spl3_50 | ~spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f424,f81,f426,f97])).
% 0.21/0.50  fof(f424,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | ~spl3_2),
% 0.21/0.50    inference(resolution,[],[f73,f82])).
% 0.21/0.50  fof(f417,plain,(
% 0.21/0.50    spl3_49 | ~spl3_19 | ~spl3_46),
% 0.21/0.50    inference(avatar_split_clause,[],[f413,f389,f178,f415])).
% 0.21/0.50  fof(f178,plain,(
% 0.21/0.50    spl3_19 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.50  fof(f413,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_19 | ~spl3_46)),
% 0.21/0.50    inference(forward_demodulation,[],[f403,f179])).
% 0.21/0.50  fof(f179,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_19),
% 0.21/0.50    inference(avatar_component_clause,[],[f178])).
% 0.21/0.50  fof(f403,plain,(
% 0.21/0.50    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_46),
% 0.21/0.50    inference(resolution,[],[f390,f68])).
% 0.21/0.50  fof(f68,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f6])).
% 0.21/0.50  fof(f6,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.50  fof(f391,plain,(
% 0.21/0.50    ~spl3_39 | spl3_46 | ~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_45),
% 0.21/0.50    inference(avatar_split_clause,[],[f386,f368,f267,f205,f119,f115,f89,f85,f389,f314])).
% 0.21/0.50  fof(f368,plain,(
% 0.21/0.50    spl3_45 <=> ! [X1,X0] : (k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.21/0.50  fof(f386,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_45)),
% 0.21/0.50    inference(forward_demodulation,[],[f385,f206])).
% 0.21/0.50  fof(f385,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_45)),
% 0.21/0.50    inference(forward_demodulation,[],[f384,f116])).
% 0.21/0.50  fof(f384,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k1_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_45)),
% 0.21/0.50    inference(forward_demodulation,[],[f383,f268])).
% 0.21/0.50  fof(f383,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),k2_struct_0(sK0)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_45)),
% 0.21/0.50    inference(forward_demodulation,[],[f382,f120])).
% 0.21/0.50  fof(f382,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | (~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_45)),
% 0.21/0.50    inference(trivial_inequality_removal,[],[f381])).
% 0.21/0.50  fof(f381,plain,(
% 0.21/0.50    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | (~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_45)),
% 0.21/0.50    inference(forward_demodulation,[],[f380,f206])).
% 0.21/0.50  fof(f380,plain,(
% 0.21/0.50    k2_struct_0(sK1) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | (~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_45)),
% 0.21/0.50    inference(forward_demodulation,[],[f379,f116])).
% 0.21/0.50  fof(f379,plain,(
% 0.21/0.50    u1_struct_0(sK1) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | (~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_45)),
% 0.21/0.50    inference(forward_demodulation,[],[f378,f206])).
% 0.21/0.50  fof(f378,plain,(
% 0.21/0.50    u1_struct_0(sK1) != k2_struct_0(sK1) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | (~spl3_3 | ~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_45)),
% 0.21/0.50    inference(forward_demodulation,[],[f377,f86])).
% 0.21/0.50  fof(f377,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | (~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_33 | ~spl3_45)),
% 0.21/0.50    inference(forward_demodulation,[],[f376,f268])).
% 0.21/0.50  fof(f376,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | (~spl3_4 | ~spl3_10 | ~spl3_11 | ~spl3_24 | ~spl3_45)),
% 0.21/0.50    inference(forward_demodulation,[],[f375,f120])).
% 0.21/0.50  fof(f375,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_relat_1(sK2)) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | (~spl3_4 | ~spl3_10 | ~spl3_24 | ~spl3_45)),
% 0.21/0.50    inference(forward_demodulation,[],[f374,f206])).
% 0.21/0.50  fof(f374,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | (~spl3_4 | ~spl3_10 | ~spl3_45)),
% 0.21/0.50    inference(forward_demodulation,[],[f371,f116])).
% 0.21/0.50  fof(f371,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | u1_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK1),u1_struct_0(sK0)))) | (~spl3_4 | ~spl3_45)),
% 0.21/0.50    inference(resolution,[],[f369,f90])).
% 0.21/0.50  fof(f369,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_relset_1(X0,X1,sK2) != X1 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | ~spl3_45),
% 0.21/0.50    inference(avatar_component_clause,[],[f368])).
% 0.21/0.50  fof(f370,plain,(
% 0.21/0.50    ~spl3_6 | spl3_45 | ~spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f366,f81,f368,f97])).
% 0.21/0.50  fof(f366,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | ~spl3_2),
% 0.21/0.50    inference(resolution,[],[f72,f82])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f37,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f36])).
% 0.21/0.50  fof(f36,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f10])).
% 0.21/0.50  fof(f10,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.50  fof(f362,plain,(
% 0.21/0.50    ~spl3_6 | spl3_44 | ~spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f358,f81,f360,f97])).
% 0.21/0.50  fof(f358,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | v1_funct_2(k2_funct_1(sK2),X1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | ~spl3_2),
% 0.21/0.50    inference(resolution,[],[f71,f82])).
% 0.21/0.50  fof(f71,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f341,plain,(
% 0.21/0.50    spl3_43 | ~spl3_28 | ~spl3_33),
% 0.21/0.50    inference(avatar_split_clause,[],[f336,f267,f229,f339])).
% 0.21/0.50  fof(f229,plain,(
% 0.21/0.50    spl3_28 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.50  fof(f336,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_28 | ~spl3_33)),
% 0.21/0.50    inference(superposition,[],[f230,f268])).
% 0.21/0.50  fof(f230,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_28),
% 0.21/0.50    inference(avatar_component_clause,[],[f229])).
% 0.21/0.50  fof(f319,plain,(
% 0.21/0.50    spl3_39 | ~spl3_29 | ~spl3_33),
% 0.21/0.50    inference(avatar_split_clause,[],[f303,f267,f233,f314])).
% 0.21/0.50  fof(f233,plain,(
% 0.21/0.50    spl3_29 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.50  fof(f303,plain,(
% 0.21/0.50    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_29 | ~spl3_33)),
% 0.21/0.50    inference(superposition,[],[f234,f268])).
% 0.21/0.50  fof(f234,plain,(
% 0.21/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_29),
% 0.21/0.50    inference(avatar_component_clause,[],[f233])).
% 0.21/0.50  fof(f311,plain,(
% 0.21/0.50    ~spl3_38 | spl3_13 | ~spl3_24 | ~spl3_33),
% 0.21/0.50    inference(avatar_split_clause,[],[f307,f267,f205,f131,f309])).
% 0.21/0.50  fof(f131,plain,(
% 0.21/0.50    spl3_13 <=> r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.50  fof(f307,plain,(
% 0.21/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) | (spl3_13 | ~spl3_24 | ~spl3_33)),
% 0.21/0.50    inference(forward_demodulation,[],[f299,f206])).
% 0.21/0.50  fof(f299,plain,(
% 0.21/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_struct_0(sK1),sK2)),sK2) | (spl3_13 | ~spl3_33)),
% 0.21/0.50    inference(superposition,[],[f132,f268])).
% 0.21/0.50  fof(f132,plain,(
% 0.21/0.50    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | spl3_13),
% 0.21/0.50    inference(avatar_component_clause,[],[f131])).
% 0.21/0.50  fof(f296,plain,(
% 0.21/0.50    spl3_28 | ~spl3_14 | ~spl3_24),
% 0.21/0.50    inference(avatar_split_clause,[],[f295,f205,f138,f229])).
% 0.21/0.50  fof(f138,plain,(
% 0.21/0.50    spl3_14 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.50  fof(f295,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_14 | ~spl3_24)),
% 0.21/0.50    inference(forward_demodulation,[],[f139,f206])).
% 0.21/0.50  fof(f139,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_14),
% 0.21/0.50    inference(avatar_component_clause,[],[f138])).
% 0.21/0.50  fof(f282,plain,(
% 0.21/0.50    ~spl3_14 | spl3_32),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f280])).
% 0.21/0.50  fof(f280,plain,(
% 0.21/0.50    $false | (~spl3_14 | spl3_32)),
% 0.21/0.50    inference(subsumption_resolution,[],[f139,f279])).
% 0.21/0.50  fof(f279,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))) ) | spl3_32),
% 0.21/0.50    inference(resolution,[],[f265,f69])).
% 0.21/0.50  fof(f69,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.50    inference(ennf_transformation,[],[f17])).
% 0.21/0.50  fof(f17,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.50    inference(pure_predicate_removal,[],[f5])).
% 0.21/0.50  % (10658)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.50  fof(f5,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.50  fof(f265,plain,(
% 0.21/0.50    ~v4_relat_1(sK2,k2_struct_0(sK0)) | spl3_32),
% 0.21/0.50    inference(avatar_component_clause,[],[f264])).
% 0.21/0.50  fof(f264,plain,(
% 0.21/0.50    spl3_32 <=> v4_relat_1(sK2,k2_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.50  fof(f277,plain,(
% 0.21/0.50    ~spl3_6 | spl3_34 | spl3_35 | ~spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f270,f81,f275,f272,f97])).
% 0.21/0.50  fof(f270,plain,(
% 0.21/0.50    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | ~spl3_2),
% 0.21/0.50    inference(resolution,[],[f70,f82])).
% 0.21/0.50  fof(f70,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f37])).
% 0.21/0.50  fof(f269,plain,(
% 0.21/0.50    ~spl3_16 | ~spl3_32 | spl3_33 | ~spl3_31),
% 0.21/0.50    inference(avatar_split_clause,[],[f262,f258,f267,f264,f156])).
% 0.21/0.50  fof(f258,plain,(
% 0.21/0.50    spl3_31 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.50  fof(f262,plain,(
% 0.21/0.50    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v4_relat_1(sK2,k2_struct_0(sK0)) | ~v1_relat_1(sK2) | ~spl3_31),
% 0.21/0.50    inference(resolution,[],[f259,f66])).
% 0.21/0.50  fof(f66,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f46])).
% 0.21/0.50  fof(f46,plain,(
% 0.21/0.50    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(nnf_transformation,[],[f33])).
% 0.21/0.50  fof(f33,plain,(
% 0.21/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.50    inference(flattening,[],[f32])).
% 0.21/0.50  fof(f32,plain,(
% 0.21/0.50    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.50    inference(ennf_transformation,[],[f8])).
% 0.21/0.50  % (10659)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.50  fof(f8,axiom,(
% 0.21/0.50    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.50  fof(f259,plain,(
% 0.21/0.50    v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_31),
% 0.21/0.50    inference(avatar_component_clause,[],[f258])).
% 0.21/0.50  fof(f261,plain,(
% 0.21/0.50    spl3_31 | ~spl3_29 | ~spl3_6 | ~spl3_28 | spl3_30),
% 0.21/0.50    inference(avatar_split_clause,[],[f256,f239,f229,f97,f233,f258])).
% 0.21/0.50  fof(f239,plain,(
% 0.21/0.50    spl3_30 <=> v1_xboole_0(k2_relat_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.50  fof(f256,plain,(
% 0.21/0.50    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | v1_partfun1(sK2,k2_struct_0(sK0)) | (~spl3_6 | ~spl3_28 | spl3_30)),
% 0.21/0.50    inference(resolution,[],[f255,f230])).
% 0.21/0.50  fof(f255,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,k2_relat_1(sK2)))) | ~v1_funct_2(sK2,X0,k2_relat_1(sK2)) | v1_partfun1(sK2,X0)) ) | (~spl3_6 | spl3_30)),
% 0.21/0.50    inference(resolution,[],[f243,f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    v1_funct_1(sK2) | ~spl3_6),
% 0.21/0.50    inference(avatar_component_clause,[],[f97])).
% 0.21/0.50  fof(f243,plain,(
% 0.21/0.50    ( ! [X0,X1] : (~v1_funct_1(X0) | ~v1_funct_2(X0,X1,k2_relat_1(sK2)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,k2_relat_1(sK2)))) | v1_partfun1(X0,X1)) ) | spl3_30),
% 0.21/0.50    inference(resolution,[],[f240,f65])).
% 0.21/0.50  fof(f65,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (v1_xboole_0(X1) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_partfun1(X2,X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f31])).
% 0.21/0.50  fof(f31,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.50    inference(flattening,[],[f30])).
% 0.21/0.50  fof(f30,plain,(
% 0.21/0.50    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.50    inference(ennf_transformation,[],[f7])).
% 0.21/0.50  fof(f7,axiom,(
% 0.21/0.50    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.50  fof(f240,plain,(
% 0.21/0.50    ~v1_xboole_0(k2_relat_1(sK2)) | spl3_30),
% 0.21/0.50    inference(avatar_component_clause,[],[f239])).
% 0.21/0.50  fof(f241,plain,(
% 0.21/0.50    spl3_8 | ~spl3_7 | ~spl3_30 | ~spl3_24),
% 0.21/0.50    inference(avatar_split_clause,[],[f223,f205,f239,f101,f105])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    spl3_8 <=> v2_struct_0(sK1)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.50  fof(f223,plain,(
% 0.21/0.50    ~v1_xboole_0(k2_relat_1(sK2)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_24),
% 0.21/0.50    inference(superposition,[],[f59,f206])).
% 0.21/0.50  fof(f59,plain,(
% 0.21/0.50    ( ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f25])).
% 0.21/0.50  fof(f25,plain,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f24])).
% 0.21/0.50  fof(f24,plain,(
% 0.21/0.50    ! [X0] : (~v1_xboole_0(k2_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f12])).
% 0.21/0.50  fof(f12,axiom,(
% 0.21/0.50    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(k2_struct_0(X0)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc5_struct_0)).
% 0.21/0.50  fof(f235,plain,(
% 0.21/0.50    spl3_29 | ~spl3_15 | ~spl3_24),
% 0.21/0.50    inference(avatar_split_clause,[],[f222,f205,f143,f233])).
% 0.21/0.50  fof(f143,plain,(
% 0.21/0.50    spl3_15 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.50  fof(f222,plain,(
% 0.21/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_15 | ~spl3_24)),
% 0.21/0.50    inference(superposition,[],[f144,f206])).
% 0.21/0.50  fof(f144,plain,(
% 0.21/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_15),
% 0.21/0.50    inference(avatar_component_clause,[],[f143])).
% 0.21/0.50  fof(f216,plain,(
% 0.21/0.50    spl3_24 | ~spl3_12 | ~spl3_23),
% 0.21/0.50    inference(avatar_split_clause,[],[f214,f200,f123,f205])).
% 0.21/0.50  fof(f123,plain,(
% 0.21/0.50    spl3_12 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.50  fof(f200,plain,(
% 0.21/0.50    spl3_23 <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.50  fof(f214,plain,(
% 0.21/0.50    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_12 | ~spl3_23)),
% 0.21/0.50    inference(superposition,[],[f124,f201])).
% 0.21/0.50  fof(f201,plain,(
% 0.21/0.50    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_23),
% 0.21/0.50    inference(avatar_component_clause,[],[f200])).
% 0.21/0.50  fof(f124,plain,(
% 0.21/0.50    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_12),
% 0.21/0.50    inference(avatar_component_clause,[],[f123])).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    spl3_23 | ~spl3_4 | ~spl3_10 | ~spl3_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f198,f119,f115,f89,f200])).
% 0.21/0.50  fof(f198,plain,(
% 0.21/0.50    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | (~spl3_4 | ~spl3_10 | ~spl3_11)),
% 0.21/0.50    inference(forward_demodulation,[],[f197,f120])).
% 0.21/0.50  fof(f197,plain,(
% 0.21/0.50    k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | (~spl3_4 | ~spl3_10)),
% 0.21/0.50    inference(forward_demodulation,[],[f195,f116])).
% 0.21/0.50  fof(f195,plain,(
% 0.21/0.50    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_4),
% 0.21/0.50    inference(resolution,[],[f68,f90])).
% 0.21/0.50  fof(f180,plain,(
% 0.21/0.50    ~spl3_16 | ~spl3_6 | spl3_19 | ~spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f163,f81,f178,f97,f156])).
% 0.21/0.50  fof(f163,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_2),
% 0.21/0.50    inference(resolution,[],[f62,f82])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.50  fof(f29,plain,(
% 0.21/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f28])).
% 0.21/0.50  fof(f28,plain,(
% 0.21/0.50    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.50  fof(f176,plain,(
% 0.21/0.50    spl3_18),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f174])).
% 0.21/0.50  fof(f174,plain,(
% 0.21/0.50    $false | spl3_18),
% 0.21/0.50    inference(resolution,[],[f171,f63])).
% 0.21/0.50  fof(f63,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(k2_zfmisc_1(X0,X1))) )),
% 0.21/0.50    inference(cnf_transformation,[],[f2])).
% 0.21/0.50  fof(f2,axiom,(
% 0.21/0.50    ! [X0,X1] : v1_relat_1(k2_zfmisc_1(X0,X1))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_relat_1)).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | spl3_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f170])).
% 0.21/0.50  fof(f170,plain,(
% 0.21/0.50    spl3_18 <=> v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.50  fof(f172,plain,(
% 0.21/0.50    ~spl3_18 | ~spl3_4 | ~spl3_10 | ~spl3_11 | spl3_16),
% 0.21/0.50    inference(avatar_split_clause,[],[f168,f156,f119,f115,f89,f170])).
% 0.21/0.50  fof(f168,plain,(
% 0.21/0.50    ~v1_relat_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))) | (~spl3_4 | ~spl3_10 | ~spl3_11 | spl3_16)),
% 0.21/0.50    inference(forward_demodulation,[],[f167,f120])).
% 0.21/0.50  fof(f167,plain,(
% 0.21/0.50    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))) | (~spl3_4 | ~spl3_10 | spl3_16)),
% 0.21/0.50    inference(forward_demodulation,[],[f165,f116])).
% 0.21/0.50  fof(f165,plain,(
% 0.21/0.50    ~v1_relat_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))) | (~spl3_4 | spl3_16)),
% 0.21/0.50    inference(resolution,[],[f164,f90])).
% 0.21/0.50  fof(f164,plain,(
% 0.21/0.50    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) ) | spl3_16),
% 0.21/0.50    inference(resolution,[],[f157,f58])).
% 0.21/0.50  fof(f58,plain,(
% 0.21/0.50    ( ! [X0,X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f23])).
% 0.21/0.50  fof(f23,plain,(
% 0.21/0.50    ! [X0] : (! [X1] : (v1_relat_1(X1) | ~m1_subset_1(X1,k1_zfmisc_1(X0))) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f1])).
% 0.21/0.50  fof(f1,axiom,(
% 0.21/0.50    ! [X0] : (v1_relat_1(X0) => ! [X1] : (m1_subset_1(X1,k1_zfmisc_1(X0)) => v1_relat_1(X1)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relat_1)).
% 0.21/0.50  fof(f157,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | spl3_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f156])).
% 0.21/0.50  fof(f145,plain,(
% 0.21/0.50    spl3_15 | ~spl3_5 | ~spl3_10 | ~spl3_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f141,f119,f115,f93,f143])).
% 0.21/0.50  fof(f93,plain,(
% 0.21/0.50    spl3_5 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.50  fof(f141,plain,(
% 0.21/0.50    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_5 | ~spl3_10 | ~spl3_11)),
% 0.21/0.50    inference(forward_demodulation,[],[f128,f120])).
% 0.21/0.50  fof(f128,plain,(
% 0.21/0.50    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_5 | ~spl3_10)),
% 0.21/0.50    inference(superposition,[],[f94,f116])).
% 0.21/0.50  fof(f94,plain,(
% 0.21/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f93])).
% 0.21/0.50  fof(f140,plain,(
% 0.21/0.50    spl3_14 | ~spl3_4 | ~spl3_10 | ~spl3_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f136,f119,f115,f89,f138])).
% 0.21/0.50  fof(f136,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_10 | ~spl3_11)),
% 0.21/0.50    inference(forward_demodulation,[],[f127,f120])).
% 0.21/0.50  fof(f127,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_4 | ~spl3_10)),
% 0.21/0.50    inference(superposition,[],[f90,f116])).
% 0.21/0.50  fof(f135,plain,(
% 0.21/0.50    spl3_12 | ~spl3_3 | ~spl3_10 | ~spl3_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f134,f119,f115,f85,f123])).
% 0.21/0.50  fof(f134,plain,(
% 0.21/0.50    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_3 | ~spl3_10 | ~spl3_11)),
% 0.21/0.50    inference(forward_demodulation,[],[f126,f120])).
% 0.21/0.50  fof(f126,plain,(
% 0.21/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_3 | ~spl3_10)),
% 0.21/0.50    inference(superposition,[],[f86,f116])).
% 0.21/0.50  fof(f133,plain,(
% 0.21/0.50    ~spl3_13 | spl3_1 | ~spl3_10 | ~spl3_11),
% 0.21/0.50    inference(avatar_split_clause,[],[f129,f119,f115,f77,f131])).
% 0.21/0.50  fof(f77,plain,(
% 0.21/0.50    spl3_1 <=> r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.50  fof(f129,plain,(
% 0.21/0.50    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | (spl3_1 | ~spl3_10 | ~spl3_11)),
% 0.21/0.50    inference(forward_demodulation,[],[f125,f120])).
% 0.21/0.50  fof(f125,plain,(
% 0.21/0.50    ~r2_funct_2(u1_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) | (spl3_1 | ~spl3_10)),
% 0.21/0.50    inference(superposition,[],[f78,f116])).
% 0.21/0.50  fof(f78,plain,(
% 0.21/0.50    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) | spl3_1),
% 0.21/0.50    inference(avatar_component_clause,[],[f77])).
% 0.21/0.50  fof(f121,plain,(
% 0.21/0.50    spl3_11 | ~spl3_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f113,f109,f119])).
% 0.21/0.50  fof(f113,plain,(
% 0.21/0.50    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_9),
% 0.21/0.50    inference(resolution,[],[f56,f110])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f20])).
% 0.21/0.50  fof(f20,plain,(
% 0.21/0.50    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f11])).
% 0.21/0.50  fof(f11,axiom,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.50  fof(f117,plain,(
% 0.21/0.50    spl3_10 | ~spl3_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f112,f101,f115])).
% 0.21/0.50  fof(f112,plain,(
% 0.21/0.50    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_7),
% 0.21/0.50    inference(resolution,[],[f56,f102])).
% 0.21/0.50  fof(f111,plain,(
% 0.21/0.50    spl3_9),
% 0.21/0.50    inference(avatar_split_clause,[],[f47,f109])).
% 0.21/0.50  fof(f47,plain,(
% 0.21/0.50    l1_struct_0(sK0)),
% 0.21/0.50    inference(cnf_transformation,[],[f45])).
% 0.21/0.50  fof(f45,plain,(
% 0.21/0.50    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.21/0.50    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f19,f44,f43,f42])).
% 0.21/0.50  fof(f42,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f43,plain,(
% 0.21/0.50    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f44,plain,(
% 0.21/0.50    ? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.21/0.50    introduced(choice_axiom,[])).
% 0.21/0.50  fof(f19,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.50    inference(flattening,[],[f18])).
% 0.21/0.50  fof(f18,plain,(
% 0.21/0.50    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.21/0.50    inference(ennf_transformation,[],[f16])).
% 0.21/0.50  % (10653)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.50  fof(f16,negated_conjecture,(
% 0.21/0.50    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.21/0.50    inference(negated_conjecture,[],[f15])).
% 0.21/0.50  fof(f15,conjecture,(
% 0.21/0.50    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).
% 0.21/0.50  fof(f107,plain,(
% 0.21/0.50    ~spl3_8),
% 0.21/0.50    inference(avatar_split_clause,[],[f48,f105])).
% 0.21/0.50  fof(f48,plain,(
% 0.21/0.50    ~v2_struct_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f45])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    spl3_7),
% 0.21/0.50    inference(avatar_split_clause,[],[f49,f101])).
% 0.21/0.50  fof(f49,plain,(
% 0.21/0.50    l1_struct_0(sK1)),
% 0.21/0.50    inference(cnf_transformation,[],[f45])).
% 0.21/0.50  fof(f99,plain,(
% 0.21/0.50    spl3_6),
% 0.21/0.50    inference(avatar_split_clause,[],[f50,f97])).
% 0.21/0.50  fof(f50,plain,(
% 0.21/0.50    v1_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f45])).
% 0.21/0.50  fof(f95,plain,(
% 0.21/0.50    spl3_5),
% 0.21/0.50    inference(avatar_split_clause,[],[f51,f93])).
% 0.21/0.50  fof(f51,plain,(
% 0.21/0.50    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.50    inference(cnf_transformation,[],[f45])).
% 0.21/0.50  fof(f91,plain,(
% 0.21/0.50    spl3_4),
% 0.21/0.50    inference(avatar_split_clause,[],[f52,f89])).
% 0.21/0.50  fof(f52,plain,(
% 0.21/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.50    inference(cnf_transformation,[],[f45])).
% 0.21/0.50  fof(f87,plain,(
% 0.21/0.50    spl3_3),
% 0.21/0.50    inference(avatar_split_clause,[],[f53,f85])).
% 0.21/0.50  fof(f53,plain,(
% 0.21/0.50    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f45])).
% 0.21/0.50  fof(f83,plain,(
% 0.21/0.50    spl3_2),
% 0.21/0.50    inference(avatar_split_clause,[],[f54,f81])).
% 0.21/0.50  fof(f54,plain,(
% 0.21/0.50    v2_funct_1(sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f45])).
% 0.21/0.50  fof(f79,plain,(
% 0.21/0.50    ~spl3_1),
% 0.21/0.50    inference(avatar_split_clause,[],[f55,f77])).
% 0.21/0.50  fof(f55,plain,(
% 0.21/0.50    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.21/0.50    inference(cnf_transformation,[],[f45])).
% 0.21/0.50  % SZS output end Proof for theBenchmark
% 0.21/0.50  % (10647)------------------------------
% 0.21/0.50  % (10647)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (10647)Termination reason: Refutation
% 0.21/0.50  
% 0.21/0.50  % (10647)Memory used [KB]: 11129
% 0.21/0.50  % (10647)Time elapsed: 0.065 s
% 0.21/0.50  % (10647)------------------------------
% 0.21/0.50  % (10647)------------------------------
% 0.21/0.50  % (10653)Refutation not found, incomplete strategy% (10653)------------------------------
% 0.21/0.50  % (10653)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.50  % (10653)Termination reason: Refutation not found, incomplete strategy
% 0.21/0.50  
% 0.21/0.50  % (10653)Memory used [KB]: 6140
% 0.21/0.50  % (10653)Time elapsed: 0.086 s
% 0.21/0.50  % (10653)------------------------------
% 0.21/0.50  % (10653)------------------------------
% 0.21/0.50  % (10640)Success in time 0.144 s
%------------------------------------------------------------------------------
