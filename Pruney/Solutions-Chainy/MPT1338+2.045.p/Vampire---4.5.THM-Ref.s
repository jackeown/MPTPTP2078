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
% DateTime   : Thu Dec  3 13:14:06 EST 2020

% Result     : Theorem 0.20s
% Output     : Refutation 0.20s
% Verified   : 
% Statistics : Number of formulae       :  266 ( 577 expanded)
%              Number of leaves         :   71 ( 282 expanded)
%              Depth                    :   10
%              Number of atoms          :  931 (2416 expanded)
%              Number of equality atoms :  238 ( 721 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
% (12291)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
fof(f870,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f75,f79,f83,f87,f91,f95,f99,f103,f107,f111,f117,f121,f135,f140,f145,f152,f179,f188,f205,f220,f224,f267,f270,f330,f356,f365,f371,f384,f395,f396,f424,f432,f436,f443,f482,f497,f529,f544,f548,f552,f598,f602,f624,f650,f664,f675,f702,f710,f714,f746,f848,f869])).

fof(f869,plain,
    ( k1_xboole_0 != k4_relat_1(sK2)
    | k1_xboole_0 != k2_funct_1(sK2)
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_funct_1(sK2)
    | k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2))
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f848,plain,
    ( spl3_94
    | spl3_31
    | ~ spl3_77
    | ~ spl3_76 ),
    inference(avatar_split_clause,[],[f679,f550,f554,f258,f846])).

fof(f846,plain,
    ( spl3_94
  <=> k1_xboole_0 = k4_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_94])])).

fof(f258,plain,
    ( spl3_31
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f554,plain,
    ( spl3_77
  <=> v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).

fof(f550,plain,
    ( spl3_76
  <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).

fof(f679,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(sK2)
    | k1_xboole_0 = k4_relat_1(sK2)
    | ~ spl3_76 ),
    inference(resolution,[],[f551,f66])).

fof(f66,plain,(
    ! [X2,X0] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0)))
      | ~ v1_funct_2(X2,X0,k1_xboole_0)
      | k1_xboole_0 = X0
      | k1_xboole_0 = X2 ) ),
    inference(equality_resolution,[],[f58])).

fof(f58,plain,(
    ! [X2,X0,X1] :
      ( k1_xboole_0 = X2
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X0
      | k1_xboole_0 != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( ( ( ( ( v1_funct_2(X2,X0,X1)
              | k1_xboole_0 != X2 )
            & ( k1_xboole_0 = X2
              | ~ v1_funct_2(X2,X0,X1) ) )
          | k1_xboole_0 = X0
          | k1_xboole_0 != X1 )
        & ( ( ( v1_funct_2(X2,X0,X1)
              | k1_relset_1(X0,X1,X2) != X0 )
            & ( k1_relset_1(X0,X1,X2) = X0
              | ~ v1_funct_2(X2,X0,X1) ) )
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(nnf_transformation,[],[f26])).

fof(f26,plain,(
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
    inference(flattening,[],[f25])).

fof(f25,plain,(
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
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f551,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_xboole_0)))
    | ~ spl3_76 ),
    inference(avatar_component_clause,[],[f550])).

fof(f746,plain,
    ( ~ spl3_74
    | ~ spl3_81
    | ~ spl3_71
    | ~ spl3_43
    | spl3_77 ),
    inference(avatar_split_clause,[],[f677,f554,f363,f523,f622,f542])).

fof(f542,plain,
    ( spl3_74
  <=> v1_funct_2(sK2,k1_xboole_0,k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).

fof(f622,plain,
    ( spl3_81
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).

fof(f523,plain,
    ( spl3_71
  <=> k2_relat_1(sK2) = k2_relset_1(k1_xboole_0,k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).

fof(f363,plain,
    ( spl3_43
  <=> ! [X1,X0] :
        ( v1_funct_2(k4_relat_1(sK2),X0,X1)
        | k2_relset_1(X1,X0,sK2) != X0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK2,X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f677,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_xboole_0,k2_relat_1(sK2),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_xboole_0,k2_relat_1(sK2))
    | ~ spl3_43
    | spl3_77 ),
    inference(resolution,[],[f555,f364])).

fof(f364,plain,
    ( ! [X0,X1] :
        ( v1_funct_2(k4_relat_1(sK2),X0,X1)
        | k2_relset_1(X1,X0,sK2) != X0
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK2,X1,X0) )
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f363])).

fof(f555,plain,
    ( ~ v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_xboole_0)
    | spl3_77 ),
    inference(avatar_component_clause,[],[f554])).

fof(f714,plain,
    ( k2_struct_0(sK0) != u1_struct_0(sK0)
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k1_xboole_0 != k1_relat_1(sK2)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_relat_1(sK2) = k2_relset_1(k1_xboole_0,k2_relat_1(sK2),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f710,plain,
    ( ~ spl3_38
    | spl3_84 ),
    inference(avatar_contradiction_clause,[],[f709])).

fof(f709,plain,
    ( $false
    | ~ spl3_38
    | spl3_84 ),
    inference(subsumption_resolution,[],[f315,f708])).

fof(f708,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_84 ),
    inference(trivial_inequality_removal,[],[f707])).

fof(f707,plain,
    ( ! [X0,X1] :
        ( k1_relat_1(sK2) != k1_relat_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | spl3_84 ),
    inference(superposition,[],[f701,f170])).

fof(f170,plain,(
    ! [X2,X0,X1] :
      ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f51,f47])).

fof(f47,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) )
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => ( k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).

fof(f51,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f701,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
    | spl3_84 ),
    inference(avatar_component_clause,[],[f700])).

fof(f700,plain,
    ( spl3_84
  <=> k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).

fof(f315,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f314])).

fof(f314,plain,
    ( spl3_38
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f702,plain,
    ( ~ spl3_42
    | ~ spl3_7
    | ~ spl3_3
    | ~ spl3_84
    | spl3_49
    | ~ spl3_61 ),
    inference(avatar_split_clause,[],[f698,f480,f415,f700,f77,f93,f359])).

fof(f359,plain,
    ( spl3_42
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f93,plain,
    ( spl3_7
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f77,plain,
    ( spl3_3
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f415,plain,
    ( spl3_49
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f480,plain,
    ( spl3_61
  <=> k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).

fof(f698,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_49
    | ~ spl3_61 ),
    inference(forward_demodulation,[],[f696,f481])).

fof(f481,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2))
    | ~ spl3_61 ),
    inference(avatar_component_clause,[],[f480])).

fof(f696,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_49 ),
    inference(superposition,[],[f416,f50])).

fof(f50,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( k4_relat_1(X0) = k2_funct_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k4_relat_1(X0) = k2_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).

fof(f416,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | spl3_49 ),
    inference(avatar_component_clause,[],[f415])).

fof(f675,plain,
    ( ~ spl3_71
    | ~ spl3_81
    | ~ spl3_74
    | ~ spl3_41
    | spl3_83 ),
    inference(avatar_split_clause,[],[f669,f662,f354,f542,f622,f523])).

fof(f354,plain,
    ( spl3_41
  <=> ! [X1,X0] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | v1_funct_2(k2_funct_1(sK2),X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f662,plain,
    ( spl3_83
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).

fof(f669,plain,
    ( ~ v1_funct_2(sK2,k1_xboole_0,k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(k1_xboole_0,k2_relat_1(sK2),sK2)
    | ~ spl3_41
    | spl3_83 ),
    inference(resolution,[],[f663,f355])).

fof(f355,plain,
    ( ! [X0,X1] :
        ( v1_funct_2(k2_funct_1(sK2),X1,X0)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1 )
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f354])).

fof(f663,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_xboole_0)
    | spl3_83 ),
    inference(avatar_component_clause,[],[f662])).

fof(f664,plain,
    ( spl3_82
    | spl3_31
    | ~ spl3_83
    | ~ spl3_75 ),
    inference(avatar_split_clause,[],[f652,f546,f662,f258,f659])).

fof(f659,plain,
    ( spl3_82
  <=> k1_xboole_0 = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).

fof(f546,plain,
    ( spl3_75
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_xboole_0))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).

fof(f652,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_xboole_0)
    | k1_xboole_0 = k2_relat_1(sK2)
    | k1_xboole_0 = k2_funct_1(sK2)
    | ~ spl3_75 ),
    inference(resolution,[],[f547,f66])).

fof(f547,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_xboole_0)))
    | ~ spl3_75 ),
    inference(avatar_component_clause,[],[f546])).

fof(f650,plain,
    ( ~ spl3_49
    | spl3_2
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_24
    | ~ spl3_32
    | ~ spl3_78 ),
    inference(avatar_split_clause,[],[f649,f596,f261,f194,f119,f115,f73,f415])).

fof(f73,plain,
    ( spl3_2
  <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f115,plain,
    ( spl3_12
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f119,plain,
    ( spl3_13
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f194,plain,
    ( spl3_24
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f261,plain,
    ( spl3_32
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f596,plain,
    ( spl3_78
  <=> k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).

fof(f649,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | spl3_2
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_24
    | ~ spl3_32
    | ~ spl3_78 ),
    inference(forward_demodulation,[],[f648,f597])).

fof(f597,plain,
    ( k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | ~ spl3_78 ),
    inference(avatar_component_clause,[],[f596])).

fof(f648,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2))
    | spl3_2
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_24
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f647,f262])).

fof(f262,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f261])).

fof(f647,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl3_2
    | ~ spl3_12
    | ~ spl3_13
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f646,f120])).

fof(f120,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f119])).

fof(f646,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2))
    | spl3_2
    | ~ spl3_12
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f645,f195])).

fof(f195,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f194])).

fof(f645,plain,
    ( k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2))
    | spl3_2
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f74,f116])).

fof(f116,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f115])).

fof(f74,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f73])).

fof(f624,plain,
    ( spl3_81
    | ~ spl3_38
    | ~ spl3_51 ),
    inference(avatar_split_clause,[],[f612,f422,f314,f622])).

fof(f422,plain,
    ( spl3_51
  <=> k1_xboole_0 = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f612,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2))))
    | ~ spl3_38
    | ~ spl3_51 ),
    inference(superposition,[],[f315,f423])).

fof(f423,plain,
    ( k1_xboole_0 = k1_relat_1(sK2)
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f422])).

fof(f602,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_funct_1(sK2)
    | k2_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f598,plain,
    ( spl3_78
    | ~ spl3_39
    | ~ spl3_35
    | ~ spl3_38
    | ~ spl3_72 ),
    inference(avatar_split_clause,[],[f594,f527,f314,f278,f319,f596])).

fof(f319,plain,
    ( spl3_39
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f278,plain,
    ( spl3_35
  <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f527,plain,
    ( spl3_72
  <=> ! [X1,X0] :
        ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).

fof(f594,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | ~ spl3_35
    | ~ spl3_38
    | ~ spl3_72 ),
    inference(trivial_inequality_removal,[],[f593])).

fof(f593,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | ~ spl3_35
    | ~ spl3_38
    | ~ spl3_72 ),
    inference(forward_demodulation,[],[f592,f279])).

fof(f279,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f278])).

fof(f592,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_38
    | ~ spl3_72 ),
    inference(resolution,[],[f528,f315])).

fof(f528,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | k2_relset_1(X0,X1,sK2) != X1 )
    | ~ spl3_72 ),
    inference(avatar_component_clause,[],[f527])).

fof(f552,plain,
    ( spl3_76
    | ~ spl3_51
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f535,f434,f422,f550])).

fof(f434,plain,
    ( spl3_54
  <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f535,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_xboole_0)))
    | ~ spl3_51
    | ~ spl3_54 ),
    inference(superposition,[],[f435,f423])).

fof(f435,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f434])).

fof(f548,plain,
    ( spl3_75
    | ~ spl3_44
    | ~ spl3_51 ),
    inference(avatar_split_clause,[],[f534,f422,f393,f546])).

fof(f393,plain,
    ( spl3_44
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f534,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_xboole_0)))
    | ~ spl3_44
    | ~ spl3_51 ),
    inference(superposition,[],[f394,f423])).

fof(f394,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f393])).

fof(f544,plain,
    ( spl3_74
    | ~ spl3_39
    | ~ spl3_51 ),
    inference(avatar_split_clause,[],[f533,f422,f319,f542])).

fof(f533,plain,
    ( v1_funct_2(sK2,k1_xboole_0,k2_relat_1(sK2))
    | ~ spl3_39
    | ~ spl3_51 ),
    inference(superposition,[],[f320,f423])).

fof(f320,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f319])).

fof(f529,plain,
    ( ~ spl3_7
    | spl3_72
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f525,f77,f527,f93])).

fof(f525,plain,
    ( ! [X0,X1] :
        ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | k2_relset_1(X0,X1,sK2) != X1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_3 ),
    inference(resolution,[],[f63,f78])).

fof(f78,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f77])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

% (12304)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% (12292)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% (12306)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% (12307)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% (12310)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% (12293)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% (12309)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f497,plain,
    ( ~ spl3_38
    | spl3_63 ),
    inference(avatar_contradiction_clause,[],[f496])).

fof(f496,plain,
    ( $false
    | ~ spl3_38
    | spl3_63 ),
    inference(subsumption_resolution,[],[f315,f495])).

fof(f495,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_63 ),
    inference(trivial_inequality_removal,[],[f494])).

fof(f494,plain,
    ( ! [X0,X1] :
        ( k2_relat_1(sK2) != k2_relat_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
    | spl3_63 ),
    inference(superposition,[],[f492,f171])).

fof(f171,plain,(
    ! [X4,X5,X3] :
      ( k2_relat_1(X3) = k1_relat_1(k4_relat_1(X3))
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5))) ) ),
    inference(resolution,[],[f51,f46])).

fof(f46,plain,(
    ! [X0] :
      ( ~ v1_relat_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0)) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f492,plain,
    ( k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2))
    | spl3_63 ),
    inference(avatar_component_clause,[],[f491])).

fof(f491,plain,
    ( spl3_63
  <=> k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).

fof(f482,plain,
    ( spl3_61
    | ~ spl3_54 ),
    inference(avatar_split_clause,[],[f473,f434,f480])).

fof(f473,plain,
    ( k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2))
    | ~ spl3_54 ),
    inference(resolution,[],[f435,f53])).

fof(f53,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f443,plain,
    ( ~ spl3_38
    | ~ spl3_39
    | ~ spl3_35
    | ~ spl3_41
    | spl3_46 ),
    inference(avatar_split_clause,[],[f441,f406,f354,f278,f319,f314])).

fof(f406,plain,
    ( spl3_46
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f441,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_35
    | ~ spl3_41
    | spl3_46 ),
    inference(trivial_inequality_removal,[],[f440])).

fof(f440,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_35
    | ~ spl3_41
    | spl3_46 ),
    inference(forward_demodulation,[],[f437,f279])).

fof(f437,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_41
    | spl3_46 ),
    inference(resolution,[],[f407,f355])).

fof(f407,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | spl3_46 ),
    inference(avatar_component_clause,[],[f406])).

fof(f436,plain,
    ( ~ spl3_42
    | ~ spl3_7
    | ~ spl3_3
    | spl3_54
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f401,f393,f434,f77,f93,f359])).

fof(f401,plain,
    ( m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_44 ),
    inference(superposition,[],[f394,f50])).

fof(f432,plain,
    ( spl3_53
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f400,f393,f430])).

fof(f430,plain,
    ( spl3_53
  <=> k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f400,plain,
    ( k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_44 ),
    inference(resolution,[],[f394,f52])).

fof(f52,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f424,plain,
    ( spl3_50
    | spl3_51
    | ~ spl3_46
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f398,f393,f406,f422,f419])).

fof(f419,plain,
    ( spl3_50
  <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f398,plain,
    ( ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | k1_xboole_0 = k1_relat_1(sK2)
    | k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_44 ),
    inference(resolution,[],[f394,f54])).

fof(f54,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f35])).

fof(f396,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f395,plain,
    ( ~ spl3_7
    | ~ spl3_39
    | spl3_44
    | ~ spl3_3
    | ~ spl3_35
    | ~ spl3_38 ),
    inference(avatar_split_clause,[],[f390,f314,f278,f77,f393,f319,f93])).

fof(f390,plain,
    ( ~ v2_funct_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_35
    | ~ spl3_38 ),
    inference(trivial_inequality_removal,[],[f389])).

% (12301)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
fof(f389,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v2_funct_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_35
    | ~ spl3_38 ),
    inference(forward_demodulation,[],[f385,f279])).

fof(f385,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v2_funct_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_38 ),
    inference(resolution,[],[f315,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f384,plain,
    ( spl3_38
    | ~ spl3_28
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f383,f261,f218,f314])).

fof(f218,plain,
    ( spl3_28
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f383,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_28
    | ~ spl3_32 ),
    inference(forward_demodulation,[],[f219,f262])).

fof(f219,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f218])).

fof(f371,plain,
    ( ~ spl3_5
    | spl3_42 ),
    inference(avatar_contradiction_clause,[],[f367])).

fof(f367,plain,
    ( $false
    | ~ spl3_5
    | spl3_42 ),
    inference(subsumption_resolution,[],[f86,f366])).

fof(f366,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_42 ),
    inference(resolution,[],[f360,f51])).

fof(f360,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_42 ),
    inference(avatar_component_clause,[],[f359])).

fof(f86,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f85])).

fof(f85,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f365,plain,
    ( ~ spl3_42
    | ~ spl3_7
    | ~ spl3_3
    | spl3_43
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f357,f354,f363,f77,f93,f359])).

% (12295)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
fof(f357,plain,
    ( ! [X0,X1] :
        ( v1_funct_2(k4_relat_1(sK2),X0,X1)
        | ~ v1_funct_2(sK2,X1,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k2_relset_1(X1,X0,sK2) != X0
        | ~ v2_funct_1(sK2)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_41 ),
    inference(superposition,[],[f355,f50])).

fof(f356,plain,
    ( ~ spl3_7
    | spl3_41
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f351,f77,f354,f93])).

fof(f351,plain,
    ( ! [X0,X1] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | v1_funct_2(k2_funct_1(sK2),X1,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_3 ),
    inference(resolution,[],[f61,f78])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | v1_funct_2(k2_funct_1(X2),X1,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f330,plain,
    ( spl3_39
    | ~ spl3_29
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f305,f261,f222,f319])).

fof(f222,plain,
    ( spl3_29
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f305,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_29
    | ~ spl3_32 ),
    inference(superposition,[],[f223,f262])).

fof(f223,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f222])).

fof(f270,plain,
    ( k2_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k1_xboole_0 != k2_relat_1(sK2)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

% (12298)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
fof(f267,plain,
    ( ~ spl3_29
    | spl3_31
    | spl3_32
    | ~ spl3_16
    | ~ spl3_21
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f266,f194,f177,f138,f261,f258,f222])).

fof(f138,plain,
    ( spl3_16
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f177,plain,
    ( spl3_21
  <=> k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f266,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_16
    | ~ spl3_21
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f265,f178])).

fof(f178,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f177])).

fof(f265,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f264,f195])).

fof(f264,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k1_xboole_0 = k2_struct_0(sK1)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f245,f195])).

fof(f245,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k1_xboole_0 = k2_struct_0(sK1)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_16 ),
    inference(resolution,[],[f54,f139])).

fof(f139,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f138])).

fof(f224,plain,
    ( spl3_29
    | ~ spl3_17
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f209,f194,f143,f222])).

fof(f143,plain,
    ( spl3_17
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f209,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_17
    | ~ spl3_24 ),
    inference(superposition,[],[f144,f195])).

fof(f144,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f143])).

fof(f220,plain,
    ( spl3_28
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f208,f194,f138,f218])).

fof(f208,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(superposition,[],[f139,f195])).

fof(f205,plain,
    ( spl3_24
    | ~ spl3_14
    | ~ spl3_22 ),
    inference(avatar_split_clause,[],[f203,f186,f123,f194])).

fof(f123,plain,
    ( spl3_14
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f186,plain,
    ( spl3_22
  <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f203,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_14
    | ~ spl3_22 ),
    inference(superposition,[],[f124,f187])).

fof(f187,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_22 ),
    inference(avatar_component_clause,[],[f186])).

fof(f124,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f123])).

fof(f188,plain,
    ( spl3_22
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f184,f119,f115,f85,f186])).

fof(f184,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f183,f120])).

fof(f183,plain,
    ( k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f181,f116])).

fof(f181,plain,
    ( k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f53,f86])).

fof(f179,plain,
    ( spl3_21
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f175,f119,f115,f85,f177])).

fof(f175,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f174,f120])).

fof(f174,plain,
    ( k1_relat_1(sK2) = k1_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f172,f116])).

fof(f172,plain,
    ( k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2)
    | ~ spl3_5 ),
    inference(resolution,[],[f52,f86])).

fof(f152,plain,
    ( spl3_9
    | ~ spl3_8
    | ~ spl3_18
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f146,f115,f150,f97,f101])).

fof(f101,plain,
    ( spl3_9
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f97,plain,
    ( spl3_8
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f150,plain,
    ( spl3_18
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f146,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_12 ),
    inference(superposition,[],[f49,f116])).

fof(f49,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f18])).

fof(f18,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f145,plain,
    ( spl3_17
    | ~ spl3_6
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f141,f119,f115,f89,f143])).

fof(f89,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f141,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f128,f120])).

fof(f128,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_12 ),
    inference(superposition,[],[f90,f116])).

fof(f90,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f89])).

fof(f140,plain,
    ( spl3_16
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f136,f119,f115,f85,f138])).

fof(f136,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_5
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f127,f120])).

fof(f127,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_5
    | ~ spl3_12 ),
    inference(superposition,[],[f86,f116])).

fof(f135,plain,
    ( spl3_14
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(avatar_split_clause,[],[f134,f119,f115,f81,f123])).

fof(f81,plain,
    ( spl3_4
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

% (12308)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f134,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_12
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f126,f120])).

fof(f126,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_12 ),
    inference(superposition,[],[f82,f116])).

fof(f82,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f81])).

fof(f121,plain,
    ( spl3_13
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f113,f105,f119])).

fof(f105,plain,
    ( spl3_10
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f113,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_10 ),
    inference(resolution,[],[f48,f106])).

fof(f106,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f105])).

fof(f48,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f117,plain,
    ( spl3_12
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f112,f97,f115])).

fof(f112,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_8 ),
    inference(resolution,[],[f48,f98])).

fof(f98,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f97])).

fof(f111,plain,(
    spl3_11 ),
    inference(avatar_split_clause,[],[f45,f109])).

fof(f109,plain,
    ( spl3_11
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f45,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f107,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f36,f105])).

fof(f36,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,
    ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
      | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) )
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f33,f32,f31])).

fof(f31,plain,
    ( ? [X0] :
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
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))
                | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1)
          & ~ v2_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f32,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))
              | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) )
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1)
        & ~ v2_struct_0(X1) )
   => ( ? [X2] :
          ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))
            | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) )
          & v2_funct_1(X2)
          & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1)
      & ~ v2_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f33,plain,
    ( ? [X2] :
        ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))
          | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) )
        & v2_funct_1(X2)
        & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
        | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) )
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f15,plain,(
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
    inference(flattening,[],[f14])).

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
    inference(ennf_transformation,[],[f13])).

fof(f13,negated_conjecture,(
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
    inference(negated_conjecture,[],[f12])).

fof(f12,conjecture,(
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

fof(f103,plain,(
    ~ spl3_9 ),
    inference(avatar_split_clause,[],[f37,f101])).

fof(f37,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f99,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f38,f97])).

fof(f38,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f34])).

fof(f95,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f39,f93])).

fof(f39,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f91,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f40,f89])).

fof(f40,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f34])).

fof(f87,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f41,f85])).

fof(f41,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f34])).

fof(f83,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f42,f81])).

fof(f42,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f79,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f43,f77])).

fof(f43,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f34])).

fof(f75,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f44,f73,f70])).

fof(f70,plain,
    ( spl3_1
  <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f44,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f34])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % WCLimit    : 600
% 0.13/0.34  % DateTime   : Tue Dec  1 16:43:31 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.45  % (12303)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.45  % (12303)Refutation not found, incomplete strategy% (12303)------------------------------
% 0.20/0.45  % (12303)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.45  % (12303)Termination reason: Refutation not found, incomplete strategy
% 0.20/0.45  
% 0.20/0.45  % (12303)Memory used [KB]: 6140
% 0.20/0.45  % (12303)Time elapsed: 0.005 s
% 0.20/0.45  % (12303)------------------------------
% 0.20/0.45  % (12303)------------------------------
% 0.20/0.47  % (12299)lrs+10_4_add=off:afp=100000:afq=2.0:anc=none:bd=off:er=known:gs=on:gsem=off:irw=on:lcm=reverse:nm=4:newcnf=on:nwc=2.5:sas=z3:stl=30:sac=on:urr=ec_only:updr=off_3 on theBenchmark
% 0.20/0.47  % (12297)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.20/0.49  % (12305)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.20/0.49  % (12294)dis+1011_5:4_acc=model:afr=on:afp=10000:afq=1.4:amm=off:anc=none:bd=off:ccuc=small_ones:cond=fast:fde=unused:gs=on:nm=2:newcnf=on:nwc=1:nicw=on:sos=on:sac=on:sp=occurrence:updr=off_9 on theBenchmark
% 0.20/0.49  % (12300)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.20/0.50  % (12297)Refutation found. Thanks to Tanya!
% 0.20/0.50  % SZS status Theorem for theBenchmark
% 0.20/0.50  % SZS output start Proof for theBenchmark
% 0.20/0.50  % (12291)lrs+1_1_aac=none:acc=model:add=large:afp=100000:afq=1.2:anc=none:bd=off:bs=on:bsr=on:ccuc=first:cond=on:fde=unused:irw=on:nm=2:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:uhcvi=on_2 on theBenchmark
% 0.20/0.50  fof(f870,plain,(
% 0.20/0.50    $false),
% 0.20/0.50    inference(avatar_sat_refutation,[],[f75,f79,f83,f87,f91,f95,f99,f103,f107,f111,f117,f121,f135,f140,f145,f152,f179,f188,f205,f220,f224,f267,f270,f330,f356,f365,f371,f384,f395,f396,f424,f432,f436,f443,f482,f497,f529,f544,f548,f552,f598,f602,f624,f650,f664,f675,f702,f710,f714,f746,f848,f869])).
% 0.20/0.50  fof(f869,plain,(
% 0.20/0.50    k1_xboole_0 != k4_relat_1(sK2) | k1_xboole_0 != k2_funct_1(sK2) | k2_struct_0(sK0) != k1_relat_1(sK2) | k2_struct_0(sK0) != u1_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_funct_1(sK2) | k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) != k1_relat_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2)) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.20/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.50  fof(f848,plain,(
% 0.20/0.50    spl3_94 | spl3_31 | ~spl3_77 | ~spl3_76),
% 0.20/0.50    inference(avatar_split_clause,[],[f679,f550,f554,f258,f846])).
% 0.20/0.50  fof(f846,plain,(
% 0.20/0.50    spl3_94 <=> k1_xboole_0 = k4_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_94])])).
% 0.20/0.50  fof(f258,plain,(
% 0.20/0.50    spl3_31 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.20/0.50  fof(f554,plain,(
% 0.20/0.50    spl3_77 <=> v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).
% 0.20/0.50  fof(f550,plain,(
% 0.20/0.50    spl3_76 <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_xboole_0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).
% 0.20/0.50  fof(f679,plain,(
% 0.20/0.50    ~v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_xboole_0) | k1_xboole_0 = k2_relat_1(sK2) | k1_xboole_0 = k4_relat_1(sK2) | ~spl3_76),
% 0.20/0.50    inference(resolution,[],[f551,f66])).
% 0.20/0.50  fof(f66,plain,(
% 0.20/0.50    ( ! [X2,X0] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,k1_xboole_0))) | ~v1_funct_2(X2,X0,k1_xboole_0) | k1_xboole_0 = X0 | k1_xboole_0 = X2) )),
% 0.20/0.50    inference(equality_resolution,[],[f58])).
% 0.20/0.50  fof(f58,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X0 | k1_xboole_0 != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f35])).
% 0.20/0.50  fof(f35,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(nnf_transformation,[],[f26])).
% 0.20/0.50  fof(f26,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(flattening,[],[f25])).
% 0.20/0.50  fof(f25,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f7])).
% 0.20/0.50  fof(f7,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_funct_2)).
% 0.20/0.50  fof(f551,plain,(
% 0.20/0.50    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_xboole_0))) | ~spl3_76),
% 0.20/0.50    inference(avatar_component_clause,[],[f550])).
% 0.20/0.50  fof(f746,plain,(
% 0.20/0.50    ~spl3_74 | ~spl3_81 | ~spl3_71 | ~spl3_43 | spl3_77),
% 0.20/0.50    inference(avatar_split_clause,[],[f677,f554,f363,f523,f622,f542])).
% 0.20/0.50  fof(f542,plain,(
% 0.20/0.50    spl3_74 <=> v1_funct_2(sK2,k1_xboole_0,k2_relat_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).
% 0.20/0.50  fof(f622,plain,(
% 0.20/0.50    spl3_81 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).
% 0.20/0.50  fof(f523,plain,(
% 0.20/0.50    spl3_71 <=> k2_relat_1(sK2) = k2_relset_1(k1_xboole_0,k2_relat_1(sK2),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_71])])).
% 0.20/0.50  fof(f363,plain,(
% 0.20/0.50    spl3_43 <=> ! [X1,X0] : (v1_funct_2(k4_relat_1(sK2),X0,X1) | k2_relset_1(X1,X0,sK2) != X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK2,X1,X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 0.20/0.50  fof(f677,plain,(
% 0.20/0.50    k2_relat_1(sK2) != k2_relset_1(k1_xboole_0,k2_relat_1(sK2),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_xboole_0,k2_relat_1(sK2)) | (~spl3_43 | spl3_77)),
% 0.20/0.50    inference(resolution,[],[f555,f364])).
% 0.20/0.50  fof(f364,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_funct_2(k4_relat_1(sK2),X0,X1) | k2_relset_1(X1,X0,sK2) != X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK2,X1,X0)) ) | ~spl3_43),
% 0.20/0.50    inference(avatar_component_clause,[],[f363])).
% 0.20/0.50  fof(f555,plain,(
% 0.20/0.50    ~v1_funct_2(k4_relat_1(sK2),k2_relat_1(sK2),k1_xboole_0) | spl3_77),
% 0.20/0.50    inference(avatar_component_clause,[],[f554])).
% 0.20/0.50  fof(f714,plain,(
% 0.20/0.50    k2_struct_0(sK0) != u1_struct_0(sK0) | k2_struct_0(sK0) != k1_relat_1(sK2) | k1_xboole_0 != k1_relat_1(sK2) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_relat_1(sK2) = k2_relset_1(k1_xboole_0,k2_relat_1(sK2),sK2)),
% 0.20/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.50  fof(f710,plain,(
% 0.20/0.50    ~spl3_38 | spl3_84),
% 0.20/0.50    inference(avatar_contradiction_clause,[],[f709])).
% 0.20/0.50  fof(f709,plain,(
% 0.20/0.50    $false | (~spl3_38 | spl3_84)),
% 0.20/0.50    inference(subsumption_resolution,[],[f315,f708])).
% 0.20/0.50  fof(f708,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_84),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f707])).
% 0.20/0.50  fof(f707,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k1_relat_1(sK2) != k1_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_84),
% 0.20/0.50    inference(superposition,[],[f701,f170])).
% 0.20/0.50  fof(f170,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.20/0.50    inference(resolution,[],[f51,f47])).
% 0.20/0.50  fof(f47,plain,(
% 0.20/0.50    ( ! [X0] : (~v1_relat_1(X0) | k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f16])).
% 0.20/0.50  fof(f16,plain,(
% 0.20/0.50    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(ennf_transformation,[],[f2])).
% 0.20/0.50  fof(f2,axiom,(
% 0.20/0.50    ! [X0] : (v1_relat_1(X0) => (k1_relat_1(X0) = k2_relat_1(k4_relat_1(X0)) & k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_relat_1)).
% 0.20/0.50  fof(f51,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.20/0.50    inference(cnf_transformation,[],[f22])).
% 0.20/0.50  fof(f22,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.50    inference(ennf_transformation,[],[f4])).
% 0.20/0.50  fof(f4,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.20/0.50  fof(f701,plain,(
% 0.20/0.50    k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2)) | spl3_84),
% 0.20/0.50    inference(avatar_component_clause,[],[f700])).
% 0.20/0.50  fof(f700,plain,(
% 0.20/0.50    spl3_84 <=> k1_relat_1(sK2) = k2_relat_1(k4_relat_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_84])])).
% 0.20/0.50  fof(f315,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_38),
% 0.20/0.50    inference(avatar_component_clause,[],[f314])).
% 0.20/0.50  fof(f314,plain,(
% 0.20/0.50    spl3_38 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.20/0.50  fof(f702,plain,(
% 0.20/0.50    ~spl3_42 | ~spl3_7 | ~spl3_3 | ~spl3_84 | spl3_49 | ~spl3_61),
% 0.20/0.50    inference(avatar_split_clause,[],[f698,f480,f415,f700,f77,f93,f359])).
% 0.20/0.50  fof(f359,plain,(
% 0.20/0.50    spl3_42 <=> v1_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.20/0.50  fof(f93,plain,(
% 0.20/0.50    spl3_7 <=> v1_funct_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.20/0.50  fof(f77,plain,(
% 0.20/0.50    spl3_3 <=> v2_funct_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.20/0.50  fof(f415,plain,(
% 0.20/0.50    spl3_49 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.20/0.50  fof(f480,plain,(
% 0.20/0.50    spl3_61 <=> k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_61])])).
% 0.20/0.50  fof(f698,plain,(
% 0.20/0.50    k1_relat_1(sK2) != k2_relat_1(k4_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (spl3_49 | ~spl3_61)),
% 0.20/0.50    inference(forward_demodulation,[],[f696,f481])).
% 0.20/0.50  fof(f481,plain,(
% 0.20/0.50    k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2)) | ~spl3_61),
% 0.20/0.50    inference(avatar_component_clause,[],[f480])).
% 0.20/0.50  fof(f696,plain,(
% 0.20/0.50    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_49),
% 0.20/0.50    inference(superposition,[],[f416,f50])).
% 0.20/0.50  fof(f50,plain,(
% 0.20/0.50    ( ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f21])).
% 0.20/0.50  fof(f21,plain,(
% 0.20/0.50    ! [X0] : (k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.20/0.50    inference(flattening,[],[f20])).
% 0.20/0.50  fof(f20,plain,(
% 0.20/0.50    ! [X0] : ((k4_relat_1(X0) = k2_funct_1(X0) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.20/0.50    inference(ennf_transformation,[],[f3])).
% 0.20/0.50  fof(f3,axiom,(
% 0.20/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k4_relat_1(X0) = k2_funct_1(X0)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d9_funct_1)).
% 0.20/0.50  fof(f416,plain,(
% 0.20/0.50    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | spl3_49),
% 0.20/0.50    inference(avatar_component_clause,[],[f415])).
% 0.20/0.50  fof(f675,plain,(
% 0.20/0.50    ~spl3_71 | ~spl3_81 | ~spl3_74 | ~spl3_41 | spl3_83),
% 0.20/0.50    inference(avatar_split_clause,[],[f669,f662,f354,f542,f622,f523])).
% 0.20/0.50  fof(f354,plain,(
% 0.20/0.50    spl3_41 <=> ! [X1,X0] : (k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_funct_2(k2_funct_1(sK2),X1,X0))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.20/0.50  fof(f662,plain,(
% 0.20/0.50    spl3_83 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_xboole_0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_83])])).
% 0.20/0.50  fof(f669,plain,(
% 0.20/0.50    ~v1_funct_2(sK2,k1_xboole_0,k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(k1_xboole_0,k2_relat_1(sK2),sK2) | (~spl3_41 | spl3_83)),
% 0.20/0.50    inference(resolution,[],[f663,f355])).
% 0.20/0.50  fof(f355,plain,(
% 0.20/0.50    ( ! [X0,X1] : (v1_funct_2(k2_funct_1(sK2),X1,X0) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1) ) | ~spl3_41),
% 0.20/0.50    inference(avatar_component_clause,[],[f354])).
% 0.20/0.50  fof(f663,plain,(
% 0.20/0.50    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_xboole_0) | spl3_83),
% 0.20/0.50    inference(avatar_component_clause,[],[f662])).
% 0.20/0.50  fof(f664,plain,(
% 0.20/0.50    spl3_82 | spl3_31 | ~spl3_83 | ~spl3_75),
% 0.20/0.50    inference(avatar_split_clause,[],[f652,f546,f662,f258,f659])).
% 0.20/0.50  fof(f659,plain,(
% 0.20/0.50    spl3_82 <=> k1_xboole_0 = k2_funct_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_82])])).
% 0.20/0.50  fof(f546,plain,(
% 0.20/0.50    spl3_75 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_xboole_0)))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).
% 0.20/0.50  fof(f652,plain,(
% 0.20/0.50    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_xboole_0) | k1_xboole_0 = k2_relat_1(sK2) | k1_xboole_0 = k2_funct_1(sK2) | ~spl3_75),
% 0.20/0.50    inference(resolution,[],[f547,f66])).
% 0.20/0.50  fof(f547,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_xboole_0))) | ~spl3_75),
% 0.20/0.50    inference(avatar_component_clause,[],[f546])).
% 0.20/0.50  fof(f650,plain,(
% 0.20/0.50    ~spl3_49 | spl3_2 | ~spl3_12 | ~spl3_13 | ~spl3_24 | ~spl3_32 | ~spl3_78),
% 0.20/0.50    inference(avatar_split_clause,[],[f649,f596,f261,f194,f119,f115,f73,f415])).
% 0.20/0.50  fof(f73,plain,(
% 0.20/0.50    spl3_2 <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.20/0.50  fof(f115,plain,(
% 0.20/0.50    spl3_12 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.20/0.50  fof(f119,plain,(
% 0.20/0.50    spl3_13 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.20/0.50  fof(f194,plain,(
% 0.20/0.50    spl3_24 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.20/0.50  fof(f261,plain,(
% 0.20/0.50    spl3_32 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.20/0.50  fof(f596,plain,(
% 0.20/0.50    spl3_78 <=> k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).
% 0.20/0.50  fof(f649,plain,(
% 0.20/0.50    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (spl3_2 | ~spl3_12 | ~spl3_13 | ~spl3_24 | ~spl3_32 | ~spl3_78)),
% 0.20/0.50    inference(forward_demodulation,[],[f648,f597])).
% 0.20/0.50  fof(f597,plain,(
% 0.20/0.50    k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) | ~spl3_78),
% 0.20/0.50    inference(avatar_component_clause,[],[f596])).
% 0.20/0.50  fof(f648,plain,(
% 0.20/0.50    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)) | (spl3_2 | ~spl3_12 | ~spl3_13 | ~spl3_24 | ~spl3_32)),
% 0.20/0.50    inference(forward_demodulation,[],[f647,f262])).
% 0.20/0.50  fof(f262,plain,(
% 0.20/0.50    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_32),
% 0.20/0.50    inference(avatar_component_clause,[],[f261])).
% 0.20/0.50  fof(f647,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)) | (spl3_2 | ~spl3_12 | ~spl3_13 | ~spl3_24)),
% 0.20/0.50    inference(forward_demodulation,[],[f646,f120])).
% 0.20/0.50  fof(f120,plain,(
% 0.20/0.50    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_13),
% 0.20/0.50    inference(avatar_component_clause,[],[f119])).
% 0.20/0.50  fof(f646,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_relset_1(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)) | (spl3_2 | ~spl3_12 | ~spl3_24)),
% 0.20/0.50    inference(forward_demodulation,[],[f645,f195])).
% 0.20/0.50  fof(f195,plain,(
% 0.20/0.50    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_24),
% 0.20/0.50    inference(avatar_component_clause,[],[f194])).
% 0.20/0.50  fof(f645,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_relset_1(k2_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_struct_0(sK1),sK2)) | (spl3_2 | ~spl3_12)),
% 0.20/0.50    inference(forward_demodulation,[],[f74,f116])).
% 0.20/0.50  fof(f116,plain,(
% 0.20/0.50    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_12),
% 0.20/0.50    inference(avatar_component_clause,[],[f115])).
% 0.20/0.50  fof(f74,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | spl3_2),
% 0.20/0.50    inference(avatar_component_clause,[],[f73])).
% 0.20/0.50  fof(f624,plain,(
% 0.20/0.50    spl3_81 | ~spl3_38 | ~spl3_51),
% 0.20/0.50    inference(avatar_split_clause,[],[f612,f422,f314,f622])).
% 0.20/0.50  fof(f422,plain,(
% 0.20/0.50    spl3_51 <=> k1_xboole_0 = k1_relat_1(sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 0.20/0.50  fof(f612,plain,(
% 0.20/0.50    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_xboole_0,k2_relat_1(sK2)))) | (~spl3_38 | ~spl3_51)),
% 0.20/0.50    inference(superposition,[],[f315,f423])).
% 0.20/0.50  fof(f423,plain,(
% 0.20/0.50    k1_xboole_0 = k1_relat_1(sK2) | ~spl3_51),
% 0.20/0.50    inference(avatar_component_clause,[],[f422])).
% 0.20/0.50  fof(f602,plain,(
% 0.20/0.50    k2_struct_0(sK0) != k1_relat_1(sK2) | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) != k2_funct_1(sK2) | k2_struct_0(sK0) != u1_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.20/0.50    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.50  fof(f598,plain,(
% 0.20/0.50    spl3_78 | ~spl3_39 | ~spl3_35 | ~spl3_38 | ~spl3_72),
% 0.20/0.50    inference(avatar_split_clause,[],[f594,f527,f314,f278,f319,f596])).
% 0.20/0.50  fof(f319,plain,(
% 0.20/0.50    spl3_39 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.20/0.50  fof(f278,plain,(
% 0.20/0.50    spl3_35 <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.20/0.50  fof(f527,plain,(
% 0.20/0.50    spl3_72 <=> ! [X1,X0] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1)),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_72])])).
% 0.20/0.50  fof(f594,plain,(
% 0.20/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) | (~spl3_35 | ~spl3_38 | ~spl3_72)),
% 0.20/0.50    inference(trivial_inequality_removal,[],[f593])).
% 0.20/0.50  fof(f593,plain,(
% 0.20/0.50    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) | (~spl3_35 | ~spl3_38 | ~spl3_72)),
% 0.20/0.50    inference(forward_demodulation,[],[f592,f279])).
% 0.20/0.50  fof(f279,plain,(
% 0.20/0.50    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_35),
% 0.20/0.50    inference(avatar_component_clause,[],[f278])).
% 0.20/0.50  fof(f592,plain,(
% 0.20/0.50    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) = k2_funct_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_38 | ~spl3_72)),
% 0.20/0.50    inference(resolution,[],[f528,f315])).
% 0.20/0.50  fof(f528,plain,(
% 0.20/0.50    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1) ) | ~spl3_72),
% 0.20/0.50    inference(avatar_component_clause,[],[f527])).
% 0.20/0.50  fof(f552,plain,(
% 0.20/0.50    spl3_76 | ~spl3_51 | ~spl3_54),
% 0.20/0.50    inference(avatar_split_clause,[],[f535,f434,f422,f550])).
% 0.20/0.50  fof(f434,plain,(
% 0.20/0.50    spl3_54 <=> m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.20/0.50  fof(f535,plain,(
% 0.20/0.50    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_xboole_0))) | (~spl3_51 | ~spl3_54)),
% 0.20/0.50    inference(superposition,[],[f435,f423])).
% 0.20/0.50  fof(f435,plain,(
% 0.20/0.50    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_54),
% 0.20/0.50    inference(avatar_component_clause,[],[f434])).
% 0.20/0.50  fof(f548,plain,(
% 0.20/0.50    spl3_75 | ~spl3_44 | ~spl3_51),
% 0.20/0.50    inference(avatar_split_clause,[],[f534,f422,f393,f546])).
% 0.20/0.50  fof(f393,plain,(
% 0.20/0.50    spl3_44 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.20/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.20/0.50  fof(f534,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_xboole_0))) | (~spl3_44 | ~spl3_51)),
% 0.20/0.50    inference(superposition,[],[f394,f423])).
% 0.20/0.50  fof(f394,plain,(
% 0.20/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_44),
% 0.20/0.50    inference(avatar_component_clause,[],[f393])).
% 0.20/0.50  fof(f544,plain,(
% 0.20/0.50    spl3_74 | ~spl3_39 | ~spl3_51),
% 0.20/0.50    inference(avatar_split_clause,[],[f533,f422,f319,f542])).
% 0.20/0.50  fof(f533,plain,(
% 0.20/0.50    v1_funct_2(sK2,k1_xboole_0,k2_relat_1(sK2)) | (~spl3_39 | ~spl3_51)),
% 0.20/0.50    inference(superposition,[],[f320,f423])).
% 0.20/0.50  fof(f320,plain,(
% 0.20/0.50    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_39),
% 0.20/0.50    inference(avatar_component_clause,[],[f319])).
% 0.20/0.50  fof(f529,plain,(
% 0.20/0.50    ~spl3_7 | spl3_72 | ~spl3_3),
% 0.20/0.50    inference(avatar_split_clause,[],[f525,f77,f527,f93])).
% 0.20/0.50  fof(f525,plain,(
% 0.20/0.50    ( ! [X0,X1] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | ~spl3_3),
% 0.20/0.50    inference(resolution,[],[f63,f78])).
% 0.20/0.50  fof(f78,plain,(
% 0.20/0.50    v2_funct_1(sK2) | ~spl3_3),
% 0.20/0.50    inference(avatar_component_clause,[],[f77])).
% 0.20/0.50  fof(f63,plain,(
% 0.20/0.50    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.50    inference(cnf_transformation,[],[f30])).
% 0.20/0.50  fof(f30,plain,(
% 0.20/0.50    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.50    inference(flattening,[],[f29])).
% 0.20/0.50  fof(f29,plain,(
% 0.20/0.50    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.50    inference(ennf_transformation,[],[f11])).
% 0.20/0.50  fof(f11,axiom,(
% 0.20/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.20/0.50    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.20/0.50  % (12304)lrs+1_7_av=off:irw=on:lcm=predicate:lma=on:nm=4:newcnf=on:nwc=1:stl=30:sos=all:sp=occurrence:updr=off_81 on theBenchmark
% 0.20/0.51  % (12292)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.20/0.51  % (12306)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.20/0.51  % (12307)ott+1002_7_acc=on:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bs=unit_only:gsp=input_only:gs=on:nm=2:nwc=10:sos=theory:sp=reverse_arity:urr=on:updr=off_45 on theBenchmark
% 0.20/0.51  % (12310)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.20/0.51  % (12293)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.20/0.52  % (12309)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.20/0.52  fof(f497,plain,(
% 0.20/0.52    ~spl3_38 | spl3_63),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f496])).
% 0.20/0.52  fof(f496,plain,(
% 0.20/0.52    $false | (~spl3_38 | spl3_63)),
% 0.20/0.52    inference(subsumption_resolution,[],[f315,f495])).
% 0.20/0.52  fof(f495,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_63),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f494])).
% 0.20/0.52  fof(f494,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_relat_1(sK2) != k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_63),
% 0.20/0.52    inference(superposition,[],[f492,f171])).
% 0.20/0.52  fof(f171,plain,(
% 0.20/0.52    ( ! [X4,X5,X3] : (k2_relat_1(X3) = k1_relat_1(k4_relat_1(X3)) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X4,X5)))) )),
% 0.20/0.52    inference(resolution,[],[f51,f46])).
% 0.20/0.52  fof(f46,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_relat_1(X0) | k2_relat_1(X0) = k1_relat_1(k4_relat_1(X0))) )),
% 0.20/0.52    inference(cnf_transformation,[],[f16])).
% 0.20/0.52  fof(f492,plain,(
% 0.20/0.52    k2_relat_1(sK2) != k1_relat_1(k4_relat_1(sK2)) | spl3_63),
% 0.20/0.52    inference(avatar_component_clause,[],[f491])).
% 0.20/0.52  fof(f491,plain,(
% 0.20/0.52    spl3_63 <=> k2_relat_1(sK2) = k1_relat_1(k4_relat_1(sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_63])])).
% 0.20/0.52  fof(f482,plain,(
% 0.20/0.52    spl3_61 | ~spl3_54),
% 0.20/0.52    inference(avatar_split_clause,[],[f473,f434,f480])).
% 0.20/0.52  fof(f473,plain,(
% 0.20/0.52    k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k4_relat_1(sK2)) = k2_relat_1(k4_relat_1(sK2)) | ~spl3_54),
% 0.20/0.52    inference(resolution,[],[f435,f53])).
% 0.20/0.52  fof(f53,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f24])).
% 0.20/0.52  fof(f24,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f6])).
% 0.20/0.52  fof(f6,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.20/0.52  fof(f443,plain,(
% 0.20/0.52    ~spl3_38 | ~spl3_39 | ~spl3_35 | ~spl3_41 | spl3_46),
% 0.20/0.52    inference(avatar_split_clause,[],[f441,f406,f354,f278,f319,f314])).
% 0.20/0.52  fof(f406,plain,(
% 0.20/0.52    spl3_46 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.20/0.52  fof(f441,plain,(
% 0.20/0.52    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_35 | ~spl3_41 | spl3_46)),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f440])).
% 0.20/0.52  fof(f440,plain,(
% 0.20/0.52    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_35 | ~spl3_41 | spl3_46)),
% 0.20/0.52    inference(forward_demodulation,[],[f437,f279])).
% 0.20/0.52  fof(f437,plain,(
% 0.20/0.52    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_41 | spl3_46)),
% 0.20/0.52    inference(resolution,[],[f407,f355])).
% 0.20/0.52  fof(f407,plain,(
% 0.20/0.52    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | spl3_46),
% 0.20/0.52    inference(avatar_component_clause,[],[f406])).
% 0.20/0.52  fof(f436,plain,(
% 0.20/0.52    ~spl3_42 | ~spl3_7 | ~spl3_3 | spl3_54 | ~spl3_44),
% 0.20/0.52    inference(avatar_split_clause,[],[f401,f393,f434,f77,f93,f359])).
% 0.20/0.52  fof(f401,plain,(
% 0.20/0.52    m1_subset_1(k4_relat_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_44),
% 0.20/0.52    inference(superposition,[],[f394,f50])).
% 0.20/0.52  fof(f432,plain,(
% 0.20/0.52    spl3_53 | ~spl3_44),
% 0.20/0.52    inference(avatar_split_clause,[],[f400,f393,f430])).
% 0.20/0.52  fof(f430,plain,(
% 0.20/0.52    spl3_53 <=> k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 0.20/0.52  fof(f400,plain,(
% 0.20/0.52    k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_44),
% 0.20/0.52    inference(resolution,[],[f394,f52])).
% 0.20/0.52  fof(f52,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f23])).
% 0.20/0.52  fof(f23,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.20/0.52    inference(ennf_transformation,[],[f5])).
% 0.20/0.52  fof(f5,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.20/0.52  fof(f424,plain,(
% 0.20/0.52    spl3_50 | spl3_51 | ~spl3_46 | ~spl3_44),
% 0.20/0.52    inference(avatar_split_clause,[],[f398,f393,f406,f422,f419])).
% 0.20/0.52  fof(f419,plain,(
% 0.20/0.52    spl3_50 <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 0.20/0.52  fof(f398,plain,(
% 0.20/0.52    ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | k1_xboole_0 = k1_relat_1(sK2) | k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_44),
% 0.20/0.52    inference(resolution,[],[f394,f54])).
% 0.20/0.52  fof(f54,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.20/0.52    inference(cnf_transformation,[],[f35])).
% 0.20/0.52  fof(f396,plain,(
% 0.20/0.52    k2_struct_0(sK0) != k1_relat_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK0) != u1_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.20/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.52  fof(f395,plain,(
% 0.20/0.52    ~spl3_7 | ~spl3_39 | spl3_44 | ~spl3_3 | ~spl3_35 | ~spl3_38),
% 0.20/0.52    inference(avatar_split_clause,[],[f390,f314,f278,f77,f393,f319,f93])).
% 0.20/0.52  fof(f390,plain,(
% 0.20/0.52    ~v2_funct_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_35 | ~spl3_38)),
% 0.20/0.52    inference(trivial_inequality_removal,[],[f389])).
% 0.20/0.52  % (12301)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.20/0.52  fof(f389,plain,(
% 0.20/0.52    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v2_funct_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_35 | ~spl3_38)),
% 0.20/0.52    inference(forward_demodulation,[],[f385,f279])).
% 0.20/0.52  fof(f385,plain,(
% 0.20/0.52    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v2_funct_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~spl3_38),
% 0.20/0.52    inference(resolution,[],[f315,f62])).
% 0.20/0.52  fof(f62,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f28,plain,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.20/0.52    inference(flattening,[],[f27])).
% 0.20/0.52  fof(f27,plain,(
% 0.20/0.52    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.20/0.52    inference(ennf_transformation,[],[f8])).
% 0.20/0.52  fof(f8,axiom,(
% 0.20/0.52    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.20/0.52  fof(f384,plain,(
% 0.20/0.52    spl3_38 | ~spl3_28 | ~spl3_32),
% 0.20/0.52    inference(avatar_split_clause,[],[f383,f261,f218,f314])).
% 0.20/0.52  fof(f218,plain,(
% 0.20/0.52    spl3_28 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.20/0.52  fof(f383,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_28 | ~spl3_32)),
% 0.20/0.52    inference(forward_demodulation,[],[f219,f262])).
% 0.20/0.52  fof(f219,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_28),
% 0.20/0.52    inference(avatar_component_clause,[],[f218])).
% 0.20/0.52  fof(f371,plain,(
% 0.20/0.52    ~spl3_5 | spl3_42),
% 0.20/0.52    inference(avatar_contradiction_clause,[],[f367])).
% 0.20/0.52  fof(f367,plain,(
% 0.20/0.52    $false | (~spl3_5 | spl3_42)),
% 0.20/0.52    inference(subsumption_resolution,[],[f86,f366])).
% 0.20/0.52  fof(f366,plain,(
% 0.20/0.52    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_42),
% 0.20/0.52    inference(resolution,[],[f360,f51])).
% 0.20/0.52  fof(f360,plain,(
% 0.20/0.52    ~v1_relat_1(sK2) | spl3_42),
% 0.20/0.52    inference(avatar_component_clause,[],[f359])).
% 0.20/0.52  fof(f86,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_5),
% 0.20/0.52    inference(avatar_component_clause,[],[f85])).
% 0.20/0.52  fof(f85,plain,(
% 0.20/0.52    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.20/0.52  fof(f365,plain,(
% 0.20/0.52    ~spl3_42 | ~spl3_7 | ~spl3_3 | spl3_43 | ~spl3_41),
% 0.20/0.52    inference(avatar_split_clause,[],[f357,f354,f363,f77,f93,f359])).
% 0.20/0.52  % (12295)lrs+1011_3:1_av=off:cond=on:irw=on:lma=on:nm=16:nwc=1:stl=30:sos=all:updr=off_11 on theBenchmark
% 0.20/0.52  fof(f357,plain,(
% 0.20/0.52    ( ! [X0,X1] : (v1_funct_2(k4_relat_1(sK2),X0,X1) | ~v1_funct_2(sK2,X1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X1,X0,sK2) != X0 | ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl3_41),
% 0.20/0.52    inference(superposition,[],[f355,f50])).
% 0.20/0.52  fof(f356,plain,(
% 0.20/0.52    ~spl3_7 | spl3_41 | ~spl3_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f351,f77,f354,f93])).
% 0.20/0.52  fof(f351,plain,(
% 0.20/0.52    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | v1_funct_2(k2_funct_1(sK2),X1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | ~spl3_3),
% 0.20/0.52    inference(resolution,[],[f61,f78])).
% 0.20/0.52  fof(f61,plain,(
% 0.20/0.52    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | v1_funct_2(k2_funct_1(X2),X1,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f28])).
% 0.20/0.52  fof(f330,plain,(
% 0.20/0.52    spl3_39 | ~spl3_29 | ~spl3_32),
% 0.20/0.52    inference(avatar_split_clause,[],[f305,f261,f222,f319])).
% 0.20/0.52  fof(f222,plain,(
% 0.20/0.52    spl3_29 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.20/0.52  fof(f305,plain,(
% 0.20/0.52    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_29 | ~spl3_32)),
% 0.20/0.52    inference(superposition,[],[f223,f262])).
% 0.20/0.52  fof(f223,plain,(
% 0.20/0.52    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_29),
% 0.20/0.52    inference(avatar_component_clause,[],[f222])).
% 0.20/0.52  fof(f270,plain,(
% 0.20/0.52    k2_struct_0(sK0) != u1_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k1_xboole_0 != k2_relat_1(sK2) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v1_xboole_0(k2_struct_0(sK1)) | ~v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    introduced(theory_tautology_sat_conflict,[])).
% 0.20/0.52  % (12298)lrs+1011_5_afr=on:afp=100000:afq=1.0:amm=off:anc=none:cond=on:lma=on:nm=6:nwc=1:sas=z3:stl=30:sac=on:urr=on_12 on theBenchmark
% 0.20/0.52  fof(f267,plain,(
% 0.20/0.52    ~spl3_29 | spl3_31 | spl3_32 | ~spl3_16 | ~spl3_21 | ~spl3_24),
% 0.20/0.52    inference(avatar_split_clause,[],[f266,f194,f177,f138,f261,f258,f222])).
% 0.20/0.52  fof(f138,plain,(
% 0.20/0.52    spl3_16 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.20/0.52  fof(f177,plain,(
% 0.20/0.52    spl3_21 <=> k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.20/0.52  fof(f266,plain,(
% 0.20/0.52    k2_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_16 | ~spl3_21 | ~spl3_24)),
% 0.20/0.52    inference(forward_demodulation,[],[f265,f178])).
% 0.20/0.52  fof(f178,plain,(
% 0.20/0.52    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_21),
% 0.20/0.52    inference(avatar_component_clause,[],[f177])).
% 0.20/0.52  fof(f265,plain,(
% 0.20/0.52    k1_xboole_0 = k2_relat_1(sK2) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_16 | ~spl3_24)),
% 0.20/0.52    inference(forward_demodulation,[],[f264,f195])).
% 0.20/0.52  fof(f264,plain,(
% 0.20/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k1_xboole_0 = k2_struct_0(sK1) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_16 | ~spl3_24)),
% 0.20/0.52    inference(forward_demodulation,[],[f245,f195])).
% 0.20/0.52  fof(f245,plain,(
% 0.20/0.52    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k1_xboole_0 = k2_struct_0(sK1) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_16),
% 0.20/0.52    inference(resolution,[],[f54,f139])).
% 0.20/0.52  fof(f139,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_16),
% 0.20/0.52    inference(avatar_component_clause,[],[f138])).
% 0.20/0.52  fof(f224,plain,(
% 0.20/0.52    spl3_29 | ~spl3_17 | ~spl3_24),
% 0.20/0.52    inference(avatar_split_clause,[],[f209,f194,f143,f222])).
% 0.20/0.52  fof(f143,plain,(
% 0.20/0.52    spl3_17 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.20/0.52  fof(f209,plain,(
% 0.20/0.52    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_17 | ~spl3_24)),
% 0.20/0.52    inference(superposition,[],[f144,f195])).
% 0.20/0.52  fof(f144,plain,(
% 0.20/0.52    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_17),
% 0.20/0.52    inference(avatar_component_clause,[],[f143])).
% 0.20/0.52  fof(f220,plain,(
% 0.20/0.52    spl3_28 | ~spl3_16 | ~spl3_24),
% 0.20/0.52    inference(avatar_split_clause,[],[f208,f194,f138,f218])).
% 0.20/0.52  fof(f208,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_16 | ~spl3_24)),
% 0.20/0.52    inference(superposition,[],[f139,f195])).
% 0.20/0.52  fof(f205,plain,(
% 0.20/0.52    spl3_24 | ~spl3_14 | ~spl3_22),
% 0.20/0.52    inference(avatar_split_clause,[],[f203,f186,f123,f194])).
% 0.20/0.52  fof(f123,plain,(
% 0.20/0.52    spl3_14 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.20/0.52  fof(f186,plain,(
% 0.20/0.52    spl3_22 <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.20/0.52  fof(f203,plain,(
% 0.20/0.52    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_14 | ~spl3_22)),
% 0.20/0.52    inference(superposition,[],[f124,f187])).
% 0.20/0.52  fof(f187,plain,(
% 0.20/0.52    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_22),
% 0.20/0.52    inference(avatar_component_clause,[],[f186])).
% 0.20/0.52  fof(f124,plain,(
% 0.20/0.52    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_14),
% 0.20/0.52    inference(avatar_component_clause,[],[f123])).
% 0.20/0.52  fof(f188,plain,(
% 0.20/0.52    spl3_22 | ~spl3_5 | ~spl3_12 | ~spl3_13),
% 0.20/0.52    inference(avatar_split_clause,[],[f184,f119,f115,f85,f186])).
% 0.20/0.52  fof(f184,plain,(
% 0.20/0.52    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | (~spl3_5 | ~spl3_12 | ~spl3_13)),
% 0.20/0.52    inference(forward_demodulation,[],[f183,f120])).
% 0.20/0.52  fof(f183,plain,(
% 0.20/0.52    k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | (~spl3_5 | ~spl3_12)),
% 0.20/0.52    inference(forward_demodulation,[],[f181,f116])).
% 0.20/0.52  fof(f181,plain,(
% 0.20/0.52    k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_5),
% 0.20/0.52    inference(resolution,[],[f53,f86])).
% 0.20/0.52  fof(f179,plain,(
% 0.20/0.52    spl3_21 | ~spl3_5 | ~spl3_12 | ~spl3_13),
% 0.20/0.52    inference(avatar_split_clause,[],[f175,f119,f115,f85,f177])).
% 0.20/0.52  fof(f175,plain,(
% 0.20/0.52    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_5 | ~spl3_12 | ~spl3_13)),
% 0.20/0.52    inference(forward_demodulation,[],[f174,f120])).
% 0.20/0.52  fof(f174,plain,(
% 0.20/0.52    k1_relat_1(sK2) = k1_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_5 | ~spl3_12)),
% 0.20/0.52    inference(forward_demodulation,[],[f172,f116])).
% 0.20/0.52  fof(f172,plain,(
% 0.20/0.52    k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) = k1_relat_1(sK2) | ~spl3_5),
% 0.20/0.52    inference(resolution,[],[f52,f86])).
% 0.20/0.52  fof(f152,plain,(
% 0.20/0.52    spl3_9 | ~spl3_8 | ~spl3_18 | ~spl3_12),
% 0.20/0.52    inference(avatar_split_clause,[],[f146,f115,f150,f97,f101])).
% 0.20/0.52  fof(f101,plain,(
% 0.20/0.52    spl3_9 <=> v2_struct_0(sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.20/0.52  fof(f97,plain,(
% 0.20/0.52    spl3_8 <=> l1_struct_0(sK1)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.20/0.52  fof(f150,plain,(
% 0.20/0.52    spl3_18 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.20/0.52  fof(f146,plain,(
% 0.20/0.52    ~v1_xboole_0(k2_struct_0(sK1)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_12),
% 0.20/0.52    inference(superposition,[],[f49,f116])).
% 0.20/0.52  fof(f49,plain,(
% 0.20/0.52    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f19])).
% 0.20/0.52  fof(f19,plain,(
% 0.20/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f18])).
% 0.20/0.52  fof(f18,plain,(
% 0.20/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.20/0.52    inference(ennf_transformation,[],[f10])).
% 0.20/0.52  fof(f10,axiom,(
% 0.20/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.20/0.52  fof(f145,plain,(
% 0.20/0.52    spl3_17 | ~spl3_6 | ~spl3_12 | ~spl3_13),
% 0.20/0.52    inference(avatar_split_clause,[],[f141,f119,f115,f89,f143])).
% 0.20/0.52  fof(f89,plain,(
% 0.20/0.52    spl3_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.20/0.52  fof(f141,plain,(
% 0.20/0.52    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_6 | ~spl3_12 | ~spl3_13)),
% 0.20/0.52    inference(forward_demodulation,[],[f128,f120])).
% 0.20/0.52  fof(f128,plain,(
% 0.20/0.52    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_6 | ~spl3_12)),
% 0.20/0.52    inference(superposition,[],[f90,f116])).
% 0.20/0.52  fof(f90,plain,(
% 0.20/0.52    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_6),
% 0.20/0.52    inference(avatar_component_clause,[],[f89])).
% 0.20/0.52  fof(f140,plain,(
% 0.20/0.52    spl3_16 | ~spl3_5 | ~spl3_12 | ~spl3_13),
% 0.20/0.52    inference(avatar_split_clause,[],[f136,f119,f115,f85,f138])).
% 0.20/0.52  fof(f136,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_5 | ~spl3_12 | ~spl3_13)),
% 0.20/0.52    inference(forward_demodulation,[],[f127,f120])).
% 0.20/0.52  fof(f127,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_5 | ~spl3_12)),
% 0.20/0.52    inference(superposition,[],[f86,f116])).
% 0.20/0.52  fof(f135,plain,(
% 0.20/0.52    spl3_14 | ~spl3_4 | ~spl3_12 | ~spl3_13),
% 0.20/0.52    inference(avatar_split_clause,[],[f134,f119,f115,f81,f123])).
% 0.20/0.52  fof(f81,plain,(
% 0.20/0.52    spl3_4 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.20/0.52  % (12308)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.20/0.52  fof(f134,plain,(
% 0.20/0.52    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_12 | ~spl3_13)),
% 0.20/0.52    inference(forward_demodulation,[],[f126,f120])).
% 0.20/0.52  fof(f126,plain,(
% 0.20/0.52    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_12)),
% 0.20/0.52    inference(superposition,[],[f82,f116])).
% 0.20/0.52  fof(f82,plain,(
% 0.20/0.52    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_4),
% 0.20/0.52    inference(avatar_component_clause,[],[f81])).
% 0.20/0.52  fof(f121,plain,(
% 0.20/0.52    spl3_13 | ~spl3_10),
% 0.20/0.52    inference(avatar_split_clause,[],[f113,f105,f119])).
% 0.20/0.52  fof(f105,plain,(
% 0.20/0.52    spl3_10 <=> l1_struct_0(sK0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.20/0.52  fof(f113,plain,(
% 0.20/0.52    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_10),
% 0.20/0.52    inference(resolution,[],[f48,f106])).
% 0.20/0.52  fof(f106,plain,(
% 0.20/0.52    l1_struct_0(sK0) | ~spl3_10),
% 0.20/0.52    inference(avatar_component_clause,[],[f105])).
% 0.20/0.52  fof(f48,plain,(
% 0.20/0.52    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.20/0.52    inference(cnf_transformation,[],[f17])).
% 0.20/0.52  fof(f17,plain,(
% 0.20/0.52    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f9])).
% 0.20/0.52  fof(f9,axiom,(
% 0.20/0.52    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.20/0.52  fof(f117,plain,(
% 0.20/0.52    spl3_12 | ~spl3_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f112,f97,f115])).
% 0.20/0.52  fof(f112,plain,(
% 0.20/0.52    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_8),
% 0.20/0.52    inference(resolution,[],[f48,f98])).
% 0.20/0.52  fof(f98,plain,(
% 0.20/0.52    l1_struct_0(sK1) | ~spl3_8),
% 0.20/0.52    inference(avatar_component_clause,[],[f97])).
% 0.20/0.52  fof(f111,plain,(
% 0.20/0.52    spl3_11),
% 0.20/0.52    inference(avatar_split_clause,[],[f45,f109])).
% 0.20/0.52  fof(f109,plain,(
% 0.20/0.52    spl3_11 <=> v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.20/0.52  fof(f45,plain,(
% 0.20/0.52    v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    inference(cnf_transformation,[],[f1])).
% 0.20/0.52  fof(f1,axiom,(
% 0.20/0.52    v1_xboole_0(k1_xboole_0)),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.20/0.52  fof(f107,plain,(
% 0.20/0.52    spl3_10),
% 0.20/0.52    inference(avatar_split_clause,[],[f36,f105])).
% 0.20/0.52  fof(f36,plain,(
% 0.20/0.52    l1_struct_0(sK0)),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f34,plain,(
% 0.20/0.52    (((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.20/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f15,f33,f32,f31])).
% 0.20/0.52  fof(f31,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f32,plain,(
% 0.20/0.52    ? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f33,plain,(
% 0.20/0.52    ? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.20/0.52    introduced(choice_axiom,[])).
% 0.20/0.52  fof(f15,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.20/0.52    inference(flattening,[],[f14])).
% 0.20/0.52  fof(f14,plain,(
% 0.20/0.52    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.20/0.52    inference(ennf_transformation,[],[f13])).
% 0.20/0.52  fof(f13,negated_conjecture,(
% 0.20/0.52    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.20/0.52    inference(negated_conjecture,[],[f12])).
% 0.20/0.52  fof(f12,conjecture,(
% 0.20/0.52    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.20/0.52    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t62_tops_2)).
% 0.20/0.52  fof(f103,plain,(
% 0.20/0.52    ~spl3_9),
% 0.20/0.52    inference(avatar_split_clause,[],[f37,f101])).
% 0.20/0.52  fof(f37,plain,(
% 0.20/0.52    ~v2_struct_0(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f99,plain,(
% 0.20/0.52    spl3_8),
% 0.20/0.52    inference(avatar_split_clause,[],[f38,f97])).
% 0.20/0.52  fof(f38,plain,(
% 0.20/0.52    l1_struct_0(sK1)),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f95,plain,(
% 0.20/0.52    spl3_7),
% 0.20/0.52    inference(avatar_split_clause,[],[f39,f93])).
% 0.20/0.52  fof(f39,plain,(
% 0.20/0.52    v1_funct_1(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f91,plain,(
% 0.20/0.52    spl3_6),
% 0.20/0.52    inference(avatar_split_clause,[],[f40,f89])).
% 0.20/0.52  fof(f40,plain,(
% 0.20/0.52    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f87,plain,(
% 0.20/0.52    spl3_5),
% 0.20/0.52    inference(avatar_split_clause,[],[f41,f85])).
% 0.20/0.52  fof(f41,plain,(
% 0.20/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f83,plain,(
% 0.20/0.52    spl3_4),
% 0.20/0.52    inference(avatar_split_clause,[],[f42,f81])).
% 0.20/0.52  fof(f42,plain,(
% 0.20/0.52    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f79,plain,(
% 0.20/0.52    spl3_3),
% 0.20/0.52    inference(avatar_split_clause,[],[f43,f77])).
% 0.20/0.52  fof(f43,plain,(
% 0.20/0.52    v2_funct_1(sK2)),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  fof(f75,plain,(
% 0.20/0.52    ~spl3_1 | ~spl3_2),
% 0.20/0.52    inference(avatar_split_clause,[],[f44,f73,f70])).
% 0.20/0.52  fof(f70,plain,(
% 0.20/0.52    spl3_1 <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.20/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.20/0.52  fof(f44,plain,(
% 0.20/0.52    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.20/0.52    inference(cnf_transformation,[],[f34])).
% 0.20/0.52  % SZS output end Proof for theBenchmark
% 0.20/0.52  % (12297)------------------------------
% 0.20/0.52  % (12297)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.20/0.52  % (12297)Termination reason: Refutation
% 0.20/0.52  
% 0.20/0.52  % (12297)Memory used [KB]: 11257
% 0.20/0.52  % (12297)Time elapsed: 0.075 s
% 0.20/0.52  % (12297)------------------------------
% 0.20/0.52  % (12297)------------------------------
% 0.20/0.52  % (12311)dis+1010_10_afr=on:afp=100000:afq=2.0:amm=sco:anc=none:ep=RS:fde=unused:gs=on:nwc=1:sos=on:sac=on:sp=occurrence_3 on theBenchmark
% 0.20/0.52  % (12290)Success in time 0.166 s
%------------------------------------------------------------------------------
