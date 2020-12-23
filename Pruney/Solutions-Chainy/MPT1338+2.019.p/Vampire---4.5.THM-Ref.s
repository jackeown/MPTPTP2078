%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:02 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  275 ( 555 expanded)
%              Number of leaves         :   69 ( 263 expanded)
%              Depth                    :   10
%              Number of atoms          :  966 (2272 expanded)
%              Number of equality atoms :  201 ( 582 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f713,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f108,f112,f116,f120,f124,f128,f132,f136,f140,f147,f151,f166,f176,f182,f214,f219,f223,f248,f261,f275,f279,f283,f332,f346,f368,f374,f383,f385,f411,f419,f438,f486,f494,f561,f575,f582,f620,f635,f653,f658,f670,f685,f699,f711,f712])).

fof(f712,plain,
    ( k2_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_funct_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f711,plain,
    ( k2_struct_0(sK0) != k1_relat_1(sK2)
    | k2_funct_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k2_struct_0(sK0) != u1_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f699,plain,
    ( ~ spl3_59
    | spl3_81
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_26
    | ~ spl3_39
    | ~ spl3_80 ),
    inference(avatar_split_clause,[],[f695,f683,f329,f250,f169,f153,f697,f476])).

fof(f476,plain,
    ( spl3_59
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f697,plain,
    ( spl3_81
  <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).

fof(f153,plain,
    ( spl3_13
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f169,plain,
    ( spl3_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f250,plain,
    ( spl3_26
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f329,plain,
    ( spl3_39
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).

fof(f683,plain,
    ( spl3_80
  <=> ! [X1,X0] :
        ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).

% (16447)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f695,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_26
    | ~ spl3_39
    | ~ spl3_80 ),
    inference(trivial_inequality_removal,[],[f694])).

fof(f694,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_26
    | ~ spl3_39
    | ~ spl3_80 ),
    inference(forward_demodulation,[],[f693,f154])).

fof(f154,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f153])).

fof(f693,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_15
    | ~ spl3_26
    | ~ spl3_39
    | ~ spl3_80 ),
    inference(forward_demodulation,[],[f692,f330])).

fof(f330,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_39 ),
    inference(avatar_component_clause,[],[f329])).

% (16463)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
fof(f692,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_15
    | ~ spl3_26
    | ~ spl3_39
    | ~ spl3_80 ),
    inference(forward_demodulation,[],[f691,f251])).

fof(f251,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f250])).

fof(f691,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_15
    | ~ spl3_26
    | ~ spl3_39
    | ~ spl3_80 ),
    inference(forward_demodulation,[],[f690,f330])).

fof(f690,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_15
    | ~ spl3_26
    | ~ spl3_80 ),
    inference(forward_demodulation,[],[f687,f251])).

fof(f687,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_15
    | ~ spl3_80 ),
    inference(resolution,[],[f684,f170])).

fof(f170,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f169])).

fof(f684,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | k2_relset_1(X0,X1,sK2) != X1 )
    | ~ spl3_80 ),
    inference(avatar_component_clause,[],[f683])).

fof(f685,plain,
    ( ~ spl3_7
    | spl3_80
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f680,f110,f683,f126])).

fof(f126,plain,
    ( spl3_7
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f110,plain,
    ( spl3_3
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f680,plain,
    ( ! [X0,X1] :
        ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | k2_relset_1(X0,X1,sK2) != X1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_3 ),
    inference(resolution,[],[f99,f111])).

fof(f111,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f110])).

fof(f99,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f54])).

fof(f54,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f53])).

fof(f53,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f20])).

fof(f20,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f670,plain,
    ( ~ spl3_75
    | spl3_78
    | ~ spl3_51
    | ~ spl3_66
    | ~ spl3_76 ),
    inference(avatar_split_clause,[],[f669,f651,f579,f417,f665,f633])).

fof(f633,plain,
    ( spl3_75
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).

fof(f665,plain,
    ( spl3_78
  <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).

fof(f417,plain,
    ( spl3_51
  <=> k1_relat_1(k2_funct_1(sK2)) = k10_relat_1(k2_funct_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f579,plain,
    ( spl3_66
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).

fof(f651,plain,
    ( spl3_76
  <=> k8_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2),k1_relat_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).

fof(f669,plain,
    ( k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_51
    | ~ spl3_66
    | ~ spl3_76 ),
    inference(forward_demodulation,[],[f668,f580])).

fof(f580,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_66 ),
    inference(avatar_component_clause,[],[f579])).

fof(f668,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_51
    | ~ spl3_76 ),
    inference(forward_demodulation,[],[f660,f418])).

fof(f418,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k10_relat_1(k2_funct_1(sK2),k1_relat_1(sK2))
    | ~ spl3_51 ),
    inference(avatar_component_clause,[],[f417])).

fof(f660,plain,
    ( k10_relat_1(k2_funct_1(sK2),k1_relat_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_76 ),
    inference(superposition,[],[f100,f652])).

fof(f652,plain,
    ( k8_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2),k1_relat_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_76 ),
    inference(avatar_component_clause,[],[f651])).

fof(f100,plain,(
    ! [X2,X0,X3,X1] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,(
    ! [X0,X1,X2,X3] :
      ( k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2,X3] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).

fof(f658,plain,
    ( spl3_77
    | ~ spl3_49
    | ~ spl3_75 ),
    inference(avatar_split_clause,[],[f654,f633,f407,f656])).

fof(f656,plain,
    ( spl3_77
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).

fof(f407,plain,
    ( spl3_49
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f654,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_49
    | ~ spl3_75 ),
    inference(forward_demodulation,[],[f648,f408])).

fof(f408,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f407])).

fof(f648,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_75 ),
    inference(resolution,[],[f634,f92])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f634,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_75 ),
    inference(avatar_component_clause,[],[f633])).

fof(f653,plain,
    ( spl3_76
    | ~ spl3_75 ),
    inference(avatar_split_clause,[],[f646,f633,f651])).

fof(f646,plain,
    ( k8_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2),k1_relat_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_75 ),
    inference(resolution,[],[f634,f95])).

fof(f95,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2] :
      ( ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f14])).

fof(f14,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)
        & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).

fof(f635,plain,
    ( ~ spl3_59
    | spl3_75
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_26
    | ~ spl3_39
    | ~ spl3_74 ),
    inference(avatar_split_clause,[],[f630,f618,f329,f250,f169,f153,f633,f476])).

fof(f618,plain,
    ( spl3_74
  <=> ! [X1,X0] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).

fof(f630,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_26
    | ~ spl3_39
    | ~ spl3_74 ),
    inference(forward_demodulation,[],[f629,f251])).

fof(f629,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_26
    | ~ spl3_39
    | ~ spl3_74 ),
    inference(forward_demodulation,[],[f628,f330])).

fof(f628,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_26
    | ~ spl3_39
    | ~ spl3_74 ),
    inference(trivial_inequality_removal,[],[f627])).

fof(f627,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_13
    | ~ spl3_15
    | ~ spl3_26
    | ~ spl3_39
    | ~ spl3_74 ),
    inference(forward_demodulation,[],[f626,f154])).

fof(f626,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_15
    | ~ spl3_26
    | ~ spl3_39
    | ~ spl3_74 ),
    inference(forward_demodulation,[],[f625,f330])).

fof(f625,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_15
    | ~ spl3_26
    | ~ spl3_74 ),
    inference(forward_demodulation,[],[f622,f251])).

fof(f622,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0))))
    | ~ spl3_15
    | ~ spl3_74 ),
    inference(resolution,[],[f619,f170])).

fof(f619,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_relset_1(X0,X1,sK2) != X1
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl3_74 ),
    inference(avatar_component_clause,[],[f618])).

fof(f620,plain,
    ( ~ spl3_7
    | spl3_74
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f615,f110,f618,f126])).

fof(f615,plain,
    ( ! [X0,X1] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ v1_funct_1(sK2) )
    | ~ spl3_3 ),
    inference(resolution,[],[f98,f111])).

fof(f98,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f52])).

fof(f52,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
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

fof(f582,plain,
    ( ~ spl3_20
    | spl3_66
    | ~ spl3_65 ),
    inference(avatar_split_clause,[],[f577,f568,f579,f208])).

fof(f208,plain,
    ( spl3_20
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f568,plain,
    ( spl3_65
  <=> k1_relat_1(k2_funct_1(sK2)) = k9_relat_1(sK2,k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).

fof(f577,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_65 ),
    inference(superposition,[],[f74,f569])).

fof(f569,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ spl3_65 ),
    inference(avatar_component_clause,[],[f568])).

fof(f74,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).

fof(f575,plain,
    ( ~ spl3_22
    | spl3_65
    | ~ spl3_49
    | ~ spl3_64 ),
    inference(avatar_split_clause,[],[f574,f559,f407,f568,f231])).

fof(f231,plain,
    ( spl3_22
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f559,plain,
    ( spl3_64
  <=> ! [X0] : k10_relat_1(k2_funct_1(sK2),X0) = k9_relat_1(sK2,X0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).

fof(f574,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k9_relat_1(sK2,k1_relat_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_49
    | ~ spl3_64 ),
    inference(forward_demodulation,[],[f566,f408])).

% (16458)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
fof(f566,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k9_relat_1(sK2,k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_64 ),
    inference(superposition,[],[f73,f560])).

fof(f560,plain,
    ( ! [X0] : k10_relat_1(k2_funct_1(sK2),X0) = k9_relat_1(sK2,X0)
    | ~ spl3_64 ),
    inference(avatar_component_clause,[],[f559])).

fof(f73,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f27])).

% (16464)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
fof(f27,plain,(
    ! [X0] :
      ( k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( v1_relat_1(X0)
     => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).

fof(f561,plain,
    ( ~ spl3_20
    | ~ spl3_7
    | spl3_64
    | ~ spl3_3
    | ~ spl3_21 ),
    inference(avatar_split_clause,[],[f557,f212,f110,f559,f126,f208])).

fof(f212,plain,
    ( spl3_21
  <=> sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f557,plain,
    ( ! [X0] :
        ( k10_relat_1(k2_funct_1(sK2),X0) = k9_relat_1(sK2,X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_3
    | ~ spl3_21 ),
    inference(forward_demodulation,[],[f555,f213])).

fof(f213,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_21 ),
    inference(avatar_component_clause,[],[f212])).

fof(f555,plain,
    ( ! [X0] :
        ( k10_relat_1(k2_funct_1(sK2),X0) = k9_relat_1(k2_funct_1(k2_funct_1(sK2)),X0)
        | ~ v1_funct_1(sK2)
        | ~ v1_relat_1(sK2) )
    | ~ spl3_3 ),
    inference(resolution,[],[f392,f111])).

fof(f392,plain,(
    ! [X2,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(k2_funct_1(X1),X2) = k9_relat_1(k2_funct_1(k2_funct_1(X1)),X2)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(global_subsumption,[],[f80,f79,f387])).

fof(f387,plain,(
    ! [X2,X1] :
      ( k10_relat_1(k2_funct_1(X1),X2) = k9_relat_1(k2_funct_1(k2_funct_1(X1)),X2)
      | ~ v1_funct_1(k2_funct_1(X1))
      | ~ v1_relat_1(k2_funct_1(X1))
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f88,f78])).

fof(f78,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
    ! [X0] :
      ( ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0] :
      ( ( v2_funct_1(X0)
        & v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(k2_funct_1(X0))
        & v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).

fof(f88,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(X1)
      | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f44])).

fof(f44,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f43])).

fof(f43,plain,(
    ! [X0,X1] :
      ( k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)
      | ~ v2_funct_1(X1)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1] :
      ( ( v1_funct_1(X1)
        & v1_relat_1(X1) )
     => ( v2_funct_1(X1)
       => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).

fof(f79,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f80,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f494,plain,
    ( spl3_32
    | ~ spl3_31
    | ~ spl3_15
    | ~ spl3_26
    | ~ spl3_53 ),
    inference(avatar_split_clause,[],[f491,f436,f250,f169,f277,f281])).

fof(f281,plain,
    ( spl3_32
  <=> v1_xboole_0(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f277,plain,
    ( spl3_31
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f436,plain,
    ( spl3_53
  <=> ! [X0] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),X0)
        | v1_xboole_0(X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).

fof(f491,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | v1_xboole_0(k2_relat_1(sK2))
    | ~ spl3_15
    | ~ spl3_26
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f490,f251])).

fof(f490,plain,
    ( v1_xboole_0(k2_relat_1(sK2))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_15
    | ~ spl3_26
    | ~ spl3_53 ),
    inference(forward_demodulation,[],[f488,f251])).

fof(f488,plain,
    ( v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_15
    | ~ spl3_53 ),
    inference(resolution,[],[f437,f170])).

fof(f437,plain,
    ( ! [X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))
        | v1_xboole_0(X0)
        | ~ v1_funct_2(sK2,k2_struct_0(sK0),X0) )
    | ~ spl3_53 ),
    inference(avatar_component_clause,[],[f436])).

fof(f486,plain,
    ( spl3_59
    | ~ spl3_31
    | ~ spl3_39 ),
    inference(avatar_split_clause,[],[f462,f329,f277,f476])).

fof(f462,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_31
    | ~ spl3_39 ),
    inference(superposition,[],[f278,f330])).

fof(f278,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_31 ),
    inference(avatar_component_clause,[],[f277])).

fof(f438,plain,
    ( ~ spl3_7
    | spl3_53
    | spl3_38 ),
    inference(avatar_split_clause,[],[f434,f326,f436,f126])).

fof(f326,plain,
    ( spl3_38
  <=> v1_partfun1(sK2,k2_struct_0(sK0)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f434,plain,
    ( ! [X0] :
        ( ~ v1_funct_2(sK2,k2_struct_0(sK0),X0)
        | ~ v1_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0)))
        | v1_xboole_0(X0) )
    | spl3_38 ),
    inference(resolution,[],[f87,f327])).

fof(f327,plain,
    ( ~ v1_partfun1(sK2,k2_struct_0(sK0))
    | spl3_38 ),
    inference(avatar_component_clause,[],[f326])).

fof(f87,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_xboole_0(X1) ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(flattening,[],[f41])).

fof(f41,plain,(
    ! [X0,X1] :
      ( ! [X2] :
          ( ( v1_partfun1(X2,X0)
            & v1_funct_1(X2) )
          | ~ v1_funct_2(X2,X0,X1)
          | ~ v1_funct_1(X2)
          | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) )
      | v1_xboole_0(X1) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1] :
      ( ~ v1_xboole_0(X1)
     => ! [X2] :
          ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
         => ( ( v1_funct_2(X2,X0,X1)
              & v1_funct_1(X2) )
           => ( v1_partfun1(X2,X0)
              & v1_funct_1(X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).

% (16451)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
fof(f419,plain,
    ( ~ spl3_22
    | spl3_51
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f415,f407,f417,f231])).

fof(f415,plain,
    ( k1_relat_1(k2_funct_1(sK2)) = k10_relat_1(k2_funct_1(sK2),k1_relat_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_49 ),
    inference(superposition,[],[f73,f408])).

fof(f411,plain,
    ( spl3_49
    | ~ spl3_45 ),
    inference(avatar_split_clause,[],[f410,f366,f407])).

fof(f366,plain,
    ( spl3_45
  <=> k6_relat_1(k1_relat_1(sK2)) = k6_relat_1(k2_relat_1(k2_funct_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f410,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_45 ),
    inference(forward_demodulation,[],[f404,f70])).

fof(f70,plain,(
    ! [X0] : k1_relat_1(k6_relat_1(X0)) = X0 ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( k2_relat_1(k6_relat_1(X0)) = X0
      & k1_relat_1(k6_relat_1(X0)) = X0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).

fof(f404,plain,
    ( k1_relat_1(k6_relat_1(k1_relat_1(sK2))) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_45 ),
    inference(superposition,[],[f70,f367])).

fof(f367,plain,
    ( k6_relat_1(k1_relat_1(sK2)) = k6_relat_1(k2_relat_1(k2_funct_1(sK2)))
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f366])).

fof(f385,plain,
    ( ~ spl3_20
    | ~ spl3_7
    | ~ spl3_3
    | spl3_24 ),
    inference(avatar_split_clause,[],[f384,f237,f110,f126,f208])).

fof(f237,plain,
    ( spl3_24
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f384,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_24 ),
    inference(resolution,[],[f238,f78])).

fof(f238,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | spl3_24 ),
    inference(avatar_component_clause,[],[f237])).

fof(f383,plain,
    ( ~ spl3_20
    | ~ spl3_7
    | spl3_23 ),
    inference(avatar_split_clause,[],[f377,f234,f126,f208])).

fof(f234,plain,
    ( spl3_23
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f377,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_23 ),
    inference(resolution,[],[f235,f80])).

fof(f235,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_23 ),
    inference(avatar_component_clause,[],[f234])).

fof(f374,plain,
    ( ~ spl3_20
    | ~ spl3_7
    | spl3_22 ),
    inference(avatar_split_clause,[],[f370,f231,f126,f208])).

fof(f370,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_22 ),
    inference(resolution,[],[f232,f79])).

fof(f232,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_22 ),
    inference(avatar_component_clause,[],[f231])).

fof(f368,plain,
    ( ~ spl3_22
    | ~ spl3_23
    | ~ spl3_24
    | spl3_45
    | ~ spl3_21
    | ~ spl3_41 ),
    inference(avatar_split_clause,[],[f364,f344,f212,f366,f237,f234,f231])).

fof(f344,plain,
    ( spl3_41
  <=> k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f364,plain,
    ( k6_relat_1(k1_relat_1(sK2)) = k6_relat_1(k2_relat_1(k2_funct_1(sK2)))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_21
    | ~ spl3_41 ),
    inference(forward_demodulation,[],[f363,f345])).

fof(f345,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f344])).

fof(f363,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k2_relat_1(k2_funct_1(sK2)))
    | ~ v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_21 ),
    inference(superposition,[],[f85,f213])).

fof(f85,plain,(
    ! [X0] :
      ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f39])).

fof(f39,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).

fof(f346,plain,
    ( ~ spl3_20
    | ~ spl3_7
    | spl3_41
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f341,f110,f344,f126,f208])).

fof(f341,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f84,f111])).

fof(f84,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f332,plain,
    ( ~ spl3_38
    | spl3_39
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f324,f273,f329,f326])).

fof(f273,plain,
    ( spl3_30
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f324,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ v1_partfun1(sK2,k2_struct_0(sK0))
    | ~ spl3_30 ),
    inference(resolution,[],[f243,f274])).

fof(f274,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f273])).

fof(f243,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | k1_relat_1(X0) = X1
      | ~ v1_partfun1(X0,X1) ) ),
    inference(global_subsumption,[],[f91,f242])).

fof(f242,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_partfun1(X0,X1)
      | k1_relat_1(X0) = X1
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) ) ),
    inference(resolution,[],[f89,f93])).

fof(f93,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v4_relat_1(X2,X0) ) ),
    inference(pure_predicate_removal,[],[f11])).

fof(f11,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f89,plain,(
    ! [X0,X1] :
      ( ~ v4_relat_1(X1,X0)
      | ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f60])).

fof(f60,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f46])).

fof(f46,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f45])).

fof(f45,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0,X1] :
      ( ( v4_relat_1(X1,X0)
        & v1_relat_1(X1) )
     => ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f10])).

fof(f10,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f283,plain,
    ( ~ spl3_32
    | spl3_17
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f266,f250,f180,f281])).

fof(f180,plain,
    ( spl3_17
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f266,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_17
    | ~ spl3_26 ),
    inference(superposition,[],[f181,f251])).

fof(f181,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f180])).

fof(f279,plain,
    ( spl3_31
    | ~ spl3_16
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f265,f250,f174,f277])).

fof(f174,plain,
    ( spl3_16
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f265,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_16
    | ~ spl3_26 ),
    inference(superposition,[],[f175,f251])).

fof(f175,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f174])).

fof(f275,plain,
    ( spl3_30
    | ~ spl3_15
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f264,f250,f169,f273])).

fof(f264,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_15
    | ~ spl3_26 ),
    inference(superposition,[],[f170,f251])).

fof(f261,plain,
    ( spl3_26
    | ~ spl3_13
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f259,f246,f153,f250])).

fof(f246,plain,
    ( spl3_25
  <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f259,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_13
    | ~ spl3_25 ),
    inference(superposition,[],[f154,f247])).

fof(f247,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f246])).

fof(f248,plain,
    ( spl3_25
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f244,f169,f246])).

fof(f244,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_15 ),
    inference(resolution,[],[f92,f170])).

fof(f223,plain,
    ( spl3_15
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f222,f149,f145,f118,f169])).

fof(f118,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f145,plain,
    ( spl3_11
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f149,plain,
    ( spl3_12
  <=> k2_struct_0(sK0) = u1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f222,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_5
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f221,f150])).

fof(f150,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f149])).

fof(f221,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_5
    | ~ spl3_11 ),
    inference(forward_demodulation,[],[f119,f146])).

fof(f146,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f145])).

fof(f119,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f118])).

fof(f219,plain,
    ( ~ spl3_5
    | spl3_20 ),
    inference(avatar_contradiction_clause,[],[f217])).

fof(f217,plain,
    ( $false
    | ~ spl3_5
    | spl3_20 ),
    inference(subsumption_resolution,[],[f119,f216])).

fof(f216,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_20 ),
    inference(resolution,[],[f209,f91])).

fof(f209,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_20 ),
    inference(avatar_component_clause,[],[f208])).

fof(f214,plain,
    ( ~ spl3_20
    | ~ spl3_7
    | spl3_21
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f205,f110,f212,f126,f208])).

fof(f205,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f81,f111])).

fof(f81,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => k2_funct_1(k2_funct_1(X0)) = X0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).

fof(f182,plain,
    ( spl3_9
    | ~ spl3_8
    | ~ spl3_17
    | ~ spl3_11 ),
    inference(avatar_split_clause,[],[f159,f145,f180,f130,f134])).

fof(f134,plain,
    ( spl3_9
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f130,plain,
    ( spl3_8
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f159,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_11 ),
    inference(superposition,[],[f75,f146])).

fof(f75,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f176,plain,
    ( spl3_16
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f172,f149,f145,f122,f174])).

fof(f122,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f172,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f158,f150])).

fof(f158,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_11 ),
    inference(superposition,[],[f123,f146])).

fof(f123,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f122])).

fof(f166,plain,
    ( spl3_13
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(avatar_split_clause,[],[f165,f149,f145,f114,f153])).

fof(f114,plain,
    ( spl3_4
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f165,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_11
    | ~ spl3_12 ),
    inference(forward_demodulation,[],[f156,f150])).

fof(f156,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_11 ),
    inference(superposition,[],[f115,f146])).

fof(f115,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f114])).

fof(f151,plain,
    ( spl3_12
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f143,f138,f149])).

fof(f138,plain,
    ( spl3_10
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f143,plain,
    ( k2_struct_0(sK0) = u1_struct_0(sK0)
    | ~ spl3_10 ),
    inference(resolution,[],[f72,f139])).

fof(f139,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f138])).

fof(f72,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f147,plain,
    ( spl3_11
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f142,f130,f145])).

fof(f142,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_8 ),
    inference(resolution,[],[f72,f131])).

fof(f131,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f130])).

fof(f140,plain,(
    spl3_10 ),
    inference(avatar_split_clause,[],[f61,f138])).

fof(f61,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f59])).

fof(f59,plain,
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
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f58,f57,f56])).

% (16461)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
fof(f56,plain,
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

fof(f57,plain,
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

fof(f58,plain,
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

fof(f25,plain,(
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
    inference(flattening,[],[f24])).

% (16465)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
fof(f24,plain,(
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
    inference(ennf_transformation,[],[f22])).

fof(f22,negated_conjecture,(
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
    inference(negated_conjecture,[],[f21])).

fof(f21,conjecture,(
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

fof(f136,plain,(
    ~ spl3_9 ),
    inference(avatar_split_clause,[],[f62,f134])).

fof(f62,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f132,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f63,f130])).

fof(f63,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f59])).

fof(f128,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f64,f126])).

fof(f64,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f124,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f65,f122])).

fof(f65,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f59])).

fof(f120,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f66,f118])).

fof(f66,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f59])).

fof(f116,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f67,f114])).

fof(f67,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f112,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f68,f110])).

fof(f68,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f59])).

fof(f108,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f69,f106,f103])).

fof(f103,plain,
    ( spl3_1
  <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f106,plain,
    ( spl3_2
  <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f69,plain,
    ( k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : run_vampire %s %d
% 0.15/0.34  % Computer   : n003.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 13:06:57 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.46  % (16452)lrs+1011_10_aac=none:acc=model:add=large:afp=40000:afq=2.0:anc=none:bd=off:bsr=on:fsr=off:gs=on:gsem=off:irw=on:lcm=reverse:lwlo=on:nm=64:nwc=3:nicw=on:stl=30_38 on theBenchmark
% 0.21/0.48  % (16448)lrs+1010_2:1_aac=none:afr=on:afp=10000:afq=1.4:amm=sco:anc=none:gs=on:gsem=off:irw=on:nm=16:nwc=3:stl=30_7 on theBenchmark
% 0.21/0.49  % (16460)lrs+11_1024_afr=on:afp=40000:afq=2.0:anc=none:br=off:ep=RSTC:gs=on:nm=16:nwc=1:stl=30:sp=occurrence:urr=on_129 on theBenchmark
% 0.21/0.50  % (16456)dis+11_2:1_add=large:afp=4000:afq=1.4:amm=sco:anc=none:fsr=off:nm=16:nwc=1:sd=3:ss=axioms:st=1.2:sos=all:urr=ec_only:updr=off_2 on theBenchmark
% 0.21/0.51  % (16455)lrs+1011_3:2_aac=none:afp=10000:afq=1.2:amm=off:anc=all:cond=on:fde=none:gs=on:gsem=on:irw=on:lma=on:nm=32:newcnf=on:nwc=3:nicw=on:stl=30:sac=on:sp=reverse_arity:urr=ec_only:updr=off:uhcvi=on_5 on theBenchmark
% 0.21/0.51  % (16452)Refutation found. Thanks to Tanya!
% 0.21/0.51  % SZS status Theorem for theBenchmark
% 0.21/0.51  % SZS output start Proof for theBenchmark
% 0.21/0.51  fof(f713,plain,(
% 0.21/0.51    $false),
% 0.21/0.51    inference(avatar_sat_refutation,[],[f108,f112,f116,f120,f124,f128,f132,f136,f140,f147,f151,f166,f176,f182,f214,f219,f223,f248,f261,f275,f279,f283,f332,f346,f368,f374,f383,f385,f411,f419,f438,f486,f494,f561,f575,f582,f620,f635,f653,f658,f670,f685,f699,f711,f712])).
% 0.21/0.51  fof(f712,plain,(
% 0.21/0.51    k2_struct_0(sK0) != u1_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_funct_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_struct_0(sK0) != k1_relat_1(sK2) | k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f711,plain,(
% 0.21/0.51    k2_struct_0(sK0) != k1_relat_1(sK2) | k2_funct_1(sK2) != k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | k2_struct_0(sK0) != u1_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_relat_1(sK2) != k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f699,plain,(
% 0.21/0.51    ~spl3_59 | spl3_81 | ~spl3_13 | ~spl3_15 | ~spl3_26 | ~spl3_39 | ~spl3_80),
% 0.21/0.51    inference(avatar_split_clause,[],[f695,f683,f329,f250,f169,f153,f697,f476])).
% 0.21/0.51  fof(f476,plain,(
% 0.21/0.51    spl3_59 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 0.21/0.51  fof(f697,plain,(
% 0.21/0.51    spl3_81 <=> k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_81])])).
% 0.21/0.51  fof(f153,plain,(
% 0.21/0.51    spl3_13 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    spl3_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.51  fof(f250,plain,(
% 0.21/0.51    spl3_26 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.51  fof(f329,plain,(
% 0.21/0.51    spl3_39 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_39])])).
% 0.21/0.51  fof(f683,plain,(
% 0.21/0.51    spl3_80 <=> ! [X1,X0] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_80])])).
% 0.21/0.51  % (16447)lrs+1002_8_add=large:afp=40000:afq=1.0:amm=off:anc=none:cond=on:gs=on:irw=on:nm=16:newcnf=on:nwc=1:stl=30:sos=on:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  fof(f695,plain,(
% 0.21/0.51    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_13 | ~spl3_15 | ~spl3_26 | ~spl3_39 | ~spl3_80)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f694])).
% 0.21/0.51  fof(f694,plain,(
% 0.21/0.51    k2_struct_0(sK1) != k2_struct_0(sK1) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_13 | ~spl3_15 | ~spl3_26 | ~spl3_39 | ~spl3_80)),
% 0.21/0.51    inference(forward_demodulation,[],[f693,f154])).
% 0.21/0.51  fof(f154,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_13),
% 0.21/0.51    inference(avatar_component_clause,[],[f153])).
% 0.21/0.51  fof(f693,plain,(
% 0.21/0.51    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_15 | ~spl3_26 | ~spl3_39 | ~spl3_80)),
% 0.21/0.51    inference(forward_demodulation,[],[f692,f330])).
% 0.21/0.51  fof(f330,plain,(
% 0.21/0.51    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_39),
% 0.21/0.51    inference(avatar_component_clause,[],[f329])).
% 0.21/0.51  % (16463)ott+1_8:1_av=off:bd=preordered:bsr=on:lma=on:nm=64:newcnf=on:nwc=1.2:uhcvi=on_180 on theBenchmark
% 0.21/0.51  fof(f692,plain,(
% 0.21/0.51    k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_15 | ~spl3_26 | ~spl3_39 | ~spl3_80)),
% 0.21/0.51    inference(forward_demodulation,[],[f691,f251])).
% 0.21/0.51  fof(f251,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f250])).
% 0.21/0.51  fof(f691,plain,(
% 0.21/0.51    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_15 | ~spl3_26 | ~spl3_39 | ~spl3_80)),
% 0.21/0.51    inference(forward_demodulation,[],[f690,f330])).
% 0.21/0.51  fof(f690,plain,(
% 0.21/0.51    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_15 | ~spl3_26 | ~spl3_80)),
% 0.21/0.51    inference(forward_demodulation,[],[f687,f251])).
% 0.21/0.51  fof(f687,plain,(
% 0.21/0.51    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_funct_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_15 | ~spl3_80)),
% 0.21/0.51    inference(resolution,[],[f684,f170])).
% 0.21/0.51  fof(f170,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f169])).
% 0.21/0.51  fof(f684,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1) ) | ~spl3_80),
% 0.21/0.51    inference(avatar_component_clause,[],[f683])).
% 0.21/0.51  fof(f685,plain,(
% 0.21/0.51    ~spl3_7 | spl3_80 | ~spl3_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f680,f110,f683,f126])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    spl3_7 <=> v1_funct_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.51  fof(f110,plain,(
% 0.21/0.51    spl3_3 <=> v2_funct_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.51  fof(f680,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | ~spl3_3),
% 0.21/0.51    inference(resolution,[],[f99,f111])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    v2_funct_1(sK2) | ~spl3_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f110])).
% 0.21/0.51  fof(f99,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f54])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f53])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.21/0.51  fof(f670,plain,(
% 0.21/0.51    ~spl3_75 | spl3_78 | ~spl3_51 | ~spl3_66 | ~spl3_76),
% 0.21/0.51    inference(avatar_split_clause,[],[f669,f651,f579,f417,f665,f633])).
% 0.21/0.51  fof(f633,plain,(
% 0.21/0.51    spl3_75 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_75])])).
% 0.21/0.51  fof(f665,plain,(
% 0.21/0.51    spl3_78 <=> k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_78])])).
% 0.21/0.51  fof(f417,plain,(
% 0.21/0.51    spl3_51 <=> k1_relat_1(k2_funct_1(sK2)) = k10_relat_1(k2_funct_1(sK2),k1_relat_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 0.21/0.51  fof(f579,plain,(
% 0.21/0.51    spl3_66 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_66])])).
% 0.21/0.51  fof(f651,plain,(
% 0.21/0.51    spl3_76 <=> k8_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2),k1_relat_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_76])])).
% 0.21/0.51  fof(f669,plain,(
% 0.21/0.51    k2_relat_1(sK2) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_51 | ~spl3_66 | ~spl3_76)),
% 0.21/0.51    inference(forward_demodulation,[],[f668,f580])).
% 0.21/0.51  fof(f580,plain,(
% 0.21/0.51    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_66),
% 0.21/0.51    inference(avatar_component_clause,[],[f579])).
% 0.21/0.51  fof(f668,plain,(
% 0.21/0.51    k1_relat_1(k2_funct_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_51 | ~spl3_76)),
% 0.21/0.51    inference(forward_demodulation,[],[f660,f418])).
% 0.21/0.51  fof(f418,plain,(
% 0.21/0.51    k1_relat_1(k2_funct_1(sK2)) = k10_relat_1(k2_funct_1(sK2),k1_relat_1(sK2)) | ~spl3_51),
% 0.21/0.51    inference(avatar_component_clause,[],[f417])).
% 0.21/0.51  fof(f660,plain,(
% 0.21/0.51    k10_relat_1(k2_funct_1(sK2),k1_relat_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_76),
% 0.21/0.51    inference(superposition,[],[f100,f652])).
% 0.21/0.51  fof(f652,plain,(
% 0.21/0.51    k8_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2),k1_relat_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_76),
% 0.21/0.51    inference(avatar_component_clause,[],[f651])).
% 0.21/0.51  fof(f100,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f55])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f13])).
% 0.21/0.51  fof(f13,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k8_relset_1(X0,X1,X2,X3) = k10_relat_1(X2,X3))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k8_relset_1)).
% 0.21/0.51  fof(f658,plain,(
% 0.21/0.51    spl3_77 | ~spl3_49 | ~spl3_75),
% 0.21/0.51    inference(avatar_split_clause,[],[f654,f633,f407,f656])).
% 0.21/0.51  fof(f656,plain,(
% 0.21/0.51    spl3_77 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_77])])).
% 0.21/0.51  fof(f407,plain,(
% 0.21/0.51    spl3_49 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.21/0.51  fof(f654,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_49 | ~spl3_75)),
% 0.21/0.51    inference(forward_demodulation,[],[f648,f408])).
% 0.21/0.51  fof(f408,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_49),
% 0.21/0.51    inference(avatar_component_clause,[],[f407])).
% 0.21/0.51  fof(f648,plain,(
% 0.21/0.51    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_75),
% 0.21/0.51    inference(resolution,[],[f634,f92])).
% 0.21/0.51  fof(f92,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f48])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.51  fof(f634,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_75),
% 0.21/0.51    inference(avatar_component_clause,[],[f633])).
% 0.21/0.51  fof(f653,plain,(
% 0.21/0.51    spl3_76 | ~spl3_75),
% 0.21/0.51    inference(avatar_split_clause,[],[f646,f633,f651])).
% 0.21/0.51  fof(f646,plain,(
% 0.21/0.51    k8_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2),k1_relat_1(sK2)) = k1_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_75),
% 0.21/0.51    inference(resolution,[],[f634,f95])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f50])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f14])).
% 0.21/0.51  fof(f14,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (k8_relset_1(X0,X1,X2,X1) = k1_relset_1(X0,X1,X2) & k2_relset_1(X0,X1,X2) = k7_relset_1(X0,X1,X2,X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_relset_1)).
% 0.21/0.51  fof(f635,plain,(
% 0.21/0.51    ~spl3_59 | spl3_75 | ~spl3_13 | ~spl3_15 | ~spl3_26 | ~spl3_39 | ~spl3_74),
% 0.21/0.51    inference(avatar_split_clause,[],[f630,f618,f329,f250,f169,f153,f633,f476])).
% 0.21/0.51  fof(f618,plain,(
% 0.21/0.51    spl3_74 <=> ! [X1,X0] : (k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_74])])).
% 0.21/0.51  fof(f630,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_13 | ~spl3_15 | ~spl3_26 | ~spl3_39 | ~spl3_74)),
% 0.21/0.51    inference(forward_demodulation,[],[f629,f251])).
% 0.21/0.51  fof(f629,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k1_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_13 | ~spl3_15 | ~spl3_26 | ~spl3_39 | ~spl3_74)),
% 0.21/0.51    inference(forward_demodulation,[],[f628,f330])).
% 0.21/0.51  fof(f628,plain,(
% 0.21/0.51    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_13 | ~spl3_15 | ~spl3_26 | ~spl3_39 | ~spl3_74)),
% 0.21/0.51    inference(trivial_inequality_removal,[],[f627])).
% 0.21/0.51  fof(f627,plain,(
% 0.21/0.51    k2_struct_0(sK1) != k2_struct_0(sK1) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_13 | ~spl3_15 | ~spl3_26 | ~spl3_39 | ~spl3_74)),
% 0.21/0.51    inference(forward_demodulation,[],[f626,f154])).
% 0.21/0.51  fof(f626,plain,(
% 0.21/0.51    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_15 | ~spl3_26 | ~spl3_39 | ~spl3_74)),
% 0.21/0.51    inference(forward_demodulation,[],[f625,f330])).
% 0.21/0.51  fof(f625,plain,(
% 0.21/0.51    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_15 | ~spl3_26 | ~spl3_74)),
% 0.21/0.51    inference(forward_demodulation,[],[f622,f251])).
% 0.21/0.51  fof(f622,plain,(
% 0.21/0.51    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK1),k2_struct_0(sK0)))) | (~spl3_15 | ~spl3_74)),
% 0.21/0.51    inference(resolution,[],[f619,f170])).
% 0.21/0.51  fof(f619,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_relset_1(X0,X1,sK2) != X1 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | ~spl3_74),
% 0.21/0.51    inference(avatar_component_clause,[],[f618])).
% 0.21/0.51  fof(f620,plain,(
% 0.21/0.51    ~spl3_7 | spl3_74 | ~spl3_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f615,f110,f618,f126])).
% 0.21/0.51  fof(f615,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) ) | ~spl3_3),
% 0.21/0.51    inference(resolution,[],[f98,f111])).
% 0.21/0.51  fof(f98,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f52])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f51])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f17])).
% 0.21/0.51  fof(f17,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.51  fof(f582,plain,(
% 0.21/0.51    ~spl3_20 | spl3_66 | ~spl3_65),
% 0.21/0.51    inference(avatar_split_clause,[],[f577,f568,f579,f208])).
% 0.21/0.51  fof(f208,plain,(
% 0.21/0.51    spl3_20 <=> v1_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.51  fof(f568,plain,(
% 0.21/0.51    spl3_65 <=> k1_relat_1(k2_funct_1(sK2)) = k9_relat_1(sK2,k1_relat_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_65])])).
% 0.21/0.51  fof(f577,plain,(
% 0.21/0.51    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~spl3_65),
% 0.21/0.51    inference(superposition,[],[f74,f569])).
% 0.21/0.51  fof(f569,plain,(
% 0.21/0.51    k1_relat_1(k2_funct_1(sK2)) = k9_relat_1(sK2,k1_relat_1(sK2)) | ~spl3_65),
% 0.21/0.51    inference(avatar_component_clause,[],[f568])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0] : (k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => k9_relat_1(X0,k1_relat_1(X0)) = k2_relat_1(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t146_relat_1)).
% 0.21/0.51  fof(f575,plain,(
% 0.21/0.51    ~spl3_22 | spl3_65 | ~spl3_49 | ~spl3_64),
% 0.21/0.51    inference(avatar_split_clause,[],[f574,f559,f407,f568,f231])).
% 0.21/0.51  fof(f231,plain,(
% 0.21/0.51    spl3_22 <=> v1_relat_1(k2_funct_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.51  fof(f559,plain,(
% 0.21/0.51    spl3_64 <=> ! [X0] : k10_relat_1(k2_funct_1(sK2),X0) = k9_relat_1(sK2,X0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_64])])).
% 0.21/0.51  fof(f574,plain,(
% 0.21/0.51    k1_relat_1(k2_funct_1(sK2)) = k9_relat_1(sK2,k1_relat_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_49 | ~spl3_64)),
% 0.21/0.51    inference(forward_demodulation,[],[f566,f408])).
% 0.21/0.51  % (16458)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.51  fof(f566,plain,(
% 0.21/0.51    k1_relat_1(k2_funct_1(sK2)) = k9_relat_1(sK2,k2_relat_1(k2_funct_1(sK2))) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_64),
% 0.21/0.51    inference(superposition,[],[f73,f560])).
% 0.21/0.51  fof(f560,plain,(
% 0.21/0.51    ( ! [X0] : (k10_relat_1(k2_funct_1(sK2),X0) = k9_relat_1(sK2,X0)) ) | ~spl3_64),
% 0.21/0.51    inference(avatar_component_clause,[],[f559])).
% 0.21/0.51  fof(f73,plain,(
% 0.21/0.51    ( ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  % (16464)lrs+1002_16_av=off:cond=on:nwc=3:stl=30_83 on theBenchmark
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0] : (k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : (v1_relat_1(X0) => k1_relat_1(X0) = k10_relat_1(X0,k2_relat_1(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t169_relat_1)).
% 0.21/0.51  fof(f561,plain,(
% 0.21/0.51    ~spl3_20 | ~spl3_7 | spl3_64 | ~spl3_3 | ~spl3_21),
% 0.21/0.51    inference(avatar_split_clause,[],[f557,f212,f110,f559,f126,f208])).
% 0.21/0.51  fof(f212,plain,(
% 0.21/0.51    spl3_21 <=> sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.51  fof(f557,plain,(
% 0.21/0.51    ( ! [X0] : (k10_relat_1(k2_funct_1(sK2),X0) = k9_relat_1(sK2,X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | (~spl3_3 | ~spl3_21)),
% 0.21/0.51    inference(forward_demodulation,[],[f555,f213])).
% 0.21/0.51  fof(f213,plain,(
% 0.21/0.51    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl3_21),
% 0.21/0.51    inference(avatar_component_clause,[],[f212])).
% 0.21/0.51  fof(f555,plain,(
% 0.21/0.51    ( ! [X0] : (k10_relat_1(k2_funct_1(sK2),X0) = k9_relat_1(k2_funct_1(k2_funct_1(sK2)),X0) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)) ) | ~spl3_3),
% 0.21/0.51    inference(resolution,[],[f392,f111])).
% 0.21/0.51  fof(f392,plain,(
% 0.21/0.51    ( ! [X2,X1] : (~v2_funct_1(X1) | k10_relat_1(k2_funct_1(X1),X2) = k9_relat_1(k2_funct_1(k2_funct_1(X1)),X2) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(global_subsumption,[],[f80,f79,f387])).
% 0.21/0.51  fof(f387,plain,(
% 0.21/0.51    ( ! [X2,X1] : (k10_relat_1(k2_funct_1(X1),X2) = k9_relat_1(k2_funct_1(k2_funct_1(X1)),X2) | ~v1_funct_1(k2_funct_1(X1)) | ~v1_relat_1(k2_funct_1(X1)) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(resolution,[],[f88,f78])).
% 0.21/0.51  fof(f78,plain,(
% 0.21/0.51    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0] : ((v2_funct_1(X0) & v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(k2_funct_1(X0)) & v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc6_funct_1)).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_funct_1(X1) | k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f44])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    ! [X0,X1] : (k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1) | ~v1_funct_1(X1) | ~v1_relat_1(X1))),
% 0.21/0.51    inference(flattening,[],[f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ! [X0,X1] : ((k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0) | ~v2_funct_1(X1)) | (~v1_funct_1(X1) | ~v1_relat_1(X1)))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => (v2_funct_1(X1) => k10_relat_1(X1,X0) = k9_relat_1(k2_funct_1(X1),X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t155_funct_1)).
% 0.21/0.51  fof(f79,plain,(
% 0.21/0.51    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f34,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f34])).
% 0.21/0.51  fof(f494,plain,(
% 0.21/0.51    spl3_32 | ~spl3_31 | ~spl3_15 | ~spl3_26 | ~spl3_53),
% 0.21/0.51    inference(avatar_split_clause,[],[f491,f436,f250,f169,f277,f281])).
% 0.21/0.51  fof(f281,plain,(
% 0.21/0.51    spl3_32 <=> v1_xboole_0(k2_relat_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.51  fof(f277,plain,(
% 0.21/0.51    spl3_31 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.51  fof(f436,plain,(
% 0.21/0.51    spl3_53 <=> ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),X0) | v1_xboole_0(X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_53])])).
% 0.21/0.51  fof(f491,plain,(
% 0.21/0.51    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | v1_xboole_0(k2_relat_1(sK2)) | (~spl3_15 | ~spl3_26 | ~spl3_53)),
% 0.21/0.51    inference(forward_demodulation,[],[f490,f251])).
% 0.21/0.51  fof(f490,plain,(
% 0.21/0.51    v1_xboole_0(k2_relat_1(sK2)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_15 | ~spl3_26 | ~spl3_53)),
% 0.21/0.51    inference(forward_demodulation,[],[f488,f251])).
% 0.21/0.51  fof(f488,plain,(
% 0.21/0.51    v1_xboole_0(k2_struct_0(sK1)) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_15 | ~spl3_53)),
% 0.21/0.51    inference(resolution,[],[f437,f170])).
% 0.21/0.51  fof(f437,plain,(
% 0.21/0.51    ( ! [X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) | v1_xboole_0(X0) | ~v1_funct_2(sK2,k2_struct_0(sK0),X0)) ) | ~spl3_53),
% 0.21/0.51    inference(avatar_component_clause,[],[f436])).
% 0.21/0.51  fof(f486,plain,(
% 0.21/0.51    spl3_59 | ~spl3_31 | ~spl3_39),
% 0.21/0.51    inference(avatar_split_clause,[],[f462,f329,f277,f476])).
% 0.21/0.51  fof(f462,plain,(
% 0.21/0.51    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_31 | ~spl3_39)),
% 0.21/0.51    inference(superposition,[],[f278,f330])).
% 0.21/0.51  fof(f278,plain,(
% 0.21/0.51    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_31),
% 0.21/0.51    inference(avatar_component_clause,[],[f277])).
% 0.21/0.51  fof(f438,plain,(
% 0.21/0.51    ~spl3_7 | spl3_53 | spl3_38),
% 0.21/0.51    inference(avatar_split_clause,[],[f434,f326,f436,f126])).
% 0.21/0.51  fof(f326,plain,(
% 0.21/0.51    spl3_38 <=> v1_partfun1(sK2,k2_struct_0(sK0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.21/0.51  fof(f434,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_2(sK2,k2_struct_0(sK0),X0) | ~v1_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),X0))) | v1_xboole_0(X0)) ) | spl3_38),
% 0.21/0.51    inference(resolution,[],[f87,f327])).
% 0.21/0.51  fof(f327,plain,(
% 0.21/0.51    ~v1_partfun1(sK2,k2_struct_0(sK0)) | spl3_38),
% 0.21/0.51    inference(avatar_component_clause,[],[f326])).
% 0.21/0.51  fof(f87,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_xboole_0(X1)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : ((v1_partfun1(X2,X0) & v1_funct_1(X2)) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.51    inference(flattening,[],[f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ! [X0,X1] : (! [X2] : (((v1_partfun1(X2,X0) & v1_funct_1(X2)) | (~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) | v1_xboole_0(X1))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,axiom,(
% 0.21/0.51    ! [X0,X1] : (~v1_xboole_0(X1) => ! [X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) & v1_funct_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc5_funct_2)).
% 0.21/0.52  % (16451)dis+1011_3_awrs=decay:awrsf=32:afp=10000:afq=1.1:amm=off:anc=none:cond=fast:ep=RSTC:fde=unused:lma=on:nm=16:nwc=2.5:s2a=on:sac=on:sp=frequency:urr=ec_only_2 on theBenchmark
% 0.21/0.52  fof(f419,plain,(
% 0.21/0.52    ~spl3_22 | spl3_51 | ~spl3_49),
% 0.21/0.52    inference(avatar_split_clause,[],[f415,f407,f417,f231])).
% 0.21/0.52  fof(f415,plain,(
% 0.21/0.52    k1_relat_1(k2_funct_1(sK2)) = k10_relat_1(k2_funct_1(sK2),k1_relat_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_49),
% 0.21/0.52    inference(superposition,[],[f73,f408])).
% 0.21/0.52  fof(f411,plain,(
% 0.21/0.52    spl3_49 | ~spl3_45),
% 0.21/0.52    inference(avatar_split_clause,[],[f410,f366,f407])).
% 0.21/0.52  fof(f366,plain,(
% 0.21/0.52    spl3_45 <=> k6_relat_1(k1_relat_1(sK2)) = k6_relat_1(k2_relat_1(k2_funct_1(sK2)))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.21/0.52  fof(f410,plain,(
% 0.21/0.52    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_45),
% 0.21/0.52    inference(forward_demodulation,[],[f404,f70])).
% 0.21/0.52  fof(f70,plain,(
% 0.21/0.52    ( ! [X0] : (k1_relat_1(k6_relat_1(X0)) = X0) )),
% 0.21/0.52    inference(cnf_transformation,[],[f3])).
% 0.21/0.52  fof(f3,axiom,(
% 0.21/0.52    ! [X0] : (k2_relat_1(k6_relat_1(X0)) = X0 & k1_relat_1(k6_relat_1(X0)) = X0)),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_relat_1)).
% 0.21/0.52  fof(f404,plain,(
% 0.21/0.52    k1_relat_1(k6_relat_1(k1_relat_1(sK2))) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_45),
% 0.21/0.52    inference(superposition,[],[f70,f367])).
% 0.21/0.52  fof(f367,plain,(
% 0.21/0.52    k6_relat_1(k1_relat_1(sK2)) = k6_relat_1(k2_relat_1(k2_funct_1(sK2))) | ~spl3_45),
% 0.21/0.52    inference(avatar_component_clause,[],[f366])).
% 0.21/0.52  fof(f385,plain,(
% 0.21/0.52    ~spl3_20 | ~spl3_7 | ~spl3_3 | spl3_24),
% 0.21/0.52    inference(avatar_split_clause,[],[f384,f237,f110,f126,f208])).
% 0.21/0.52  fof(f237,plain,(
% 0.21/0.52    spl3_24 <=> v2_funct_1(k2_funct_1(sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 0.21/0.52  fof(f384,plain,(
% 0.21/0.52    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_24),
% 0.21/0.52    inference(resolution,[],[f238,f78])).
% 0.21/0.52  fof(f238,plain,(
% 0.21/0.52    ~v2_funct_1(k2_funct_1(sK2)) | spl3_24),
% 0.21/0.52    inference(avatar_component_clause,[],[f237])).
% 0.21/0.52  fof(f383,plain,(
% 0.21/0.52    ~spl3_20 | ~spl3_7 | spl3_23),
% 0.21/0.52    inference(avatar_split_clause,[],[f377,f234,f126,f208])).
% 0.21/0.52  fof(f234,plain,(
% 0.21/0.52    spl3_23 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 0.21/0.52  fof(f377,plain,(
% 0.21/0.52    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_23),
% 0.21/0.52    inference(resolution,[],[f235,f80])).
% 0.21/0.52  fof(f235,plain,(
% 0.21/0.52    ~v1_funct_1(k2_funct_1(sK2)) | spl3_23),
% 0.21/0.52    inference(avatar_component_clause,[],[f234])).
% 0.21/0.52  fof(f374,plain,(
% 0.21/0.52    ~spl3_20 | ~spl3_7 | spl3_22),
% 0.21/0.52    inference(avatar_split_clause,[],[f370,f231,f126,f208])).
% 0.21/0.52  fof(f370,plain,(
% 0.21/0.52    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_22),
% 0.21/0.52    inference(resolution,[],[f232,f79])).
% 0.21/0.52  fof(f232,plain,(
% 0.21/0.52    ~v1_relat_1(k2_funct_1(sK2)) | spl3_22),
% 0.21/0.52    inference(avatar_component_clause,[],[f231])).
% 0.21/0.52  fof(f368,plain,(
% 0.21/0.52    ~spl3_22 | ~spl3_23 | ~spl3_24 | spl3_45 | ~spl3_21 | ~spl3_41),
% 0.21/0.52    inference(avatar_split_clause,[],[f364,f344,f212,f366,f237,f234,f231])).
% 0.21/0.52  fof(f344,plain,(
% 0.21/0.52    spl3_41 <=> k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.21/0.52  fof(f364,plain,(
% 0.21/0.52    k6_relat_1(k1_relat_1(sK2)) = k6_relat_1(k2_relat_1(k2_funct_1(sK2))) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_21 | ~spl3_41)),
% 0.21/0.52    inference(forward_demodulation,[],[f363,f345])).
% 0.21/0.52  fof(f345,plain,(
% 0.21/0.52    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | ~spl3_41),
% 0.21/0.52    inference(avatar_component_clause,[],[f344])).
% 0.21/0.52  fof(f363,plain,(
% 0.21/0.52    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k2_relat_1(k2_funct_1(sK2))) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_21),
% 0.21/0.52    inference(superposition,[],[f85,f213])).
% 0.21/0.52  fof(f85,plain,(
% 0.21/0.52    ( ! [X0] : (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f40,plain,(
% 0.21/0.52    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f39])).
% 0.21/0.52  fof(f39,plain,(
% 0.21/0.52    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f8])).
% 0.21/0.52  fof(f8,axiom,(
% 0.21/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.52  fof(f346,plain,(
% 0.21/0.52    ~spl3_20 | ~spl3_7 | spl3_41 | ~spl3_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f341,f110,f344,f126,f208])).
% 0.21/0.52  fof(f341,plain,(
% 0.21/0.52    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_3),
% 0.21/0.52    inference(resolution,[],[f84,f111])).
% 0.21/0.52  fof(f84,plain,(
% 0.21/0.52    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f40])).
% 0.21/0.52  fof(f332,plain,(
% 0.21/0.52    ~spl3_38 | spl3_39 | ~spl3_30),
% 0.21/0.52    inference(avatar_split_clause,[],[f324,f273,f329,f326])).
% 0.21/0.52  fof(f273,plain,(
% 0.21/0.52    spl3_30 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.52  fof(f324,plain,(
% 0.21/0.52    k2_struct_0(sK0) = k1_relat_1(sK2) | ~v1_partfun1(sK2,k2_struct_0(sK0)) | ~spl3_30),
% 0.21/0.52    inference(resolution,[],[f243,f274])).
% 0.21/0.52  fof(f274,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_30),
% 0.21/0.52    inference(avatar_component_clause,[],[f273])).
% 0.21/0.52  fof(f243,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | k1_relat_1(X0) = X1 | ~v1_partfun1(X0,X1)) )),
% 0.21/0.52    inference(global_subsumption,[],[f91,f242])).
% 0.21/0.52  fof(f242,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (~v1_partfun1(X0,X1) | k1_relat_1(X0) = X1 | ~v1_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))) )),
% 0.21/0.52    inference(resolution,[],[f89,f93])).
% 0.21/0.52  fof(f93,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f49])).
% 0.21/0.52  fof(f49,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f23])).
% 0.21/0.52  fof(f23,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v4_relat_1(X2,X0))),
% 0.21/0.52    inference(pure_predicate_removal,[],[f11])).
% 0.21/0.52  fof(f11,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 0.21/0.52  fof(f89,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~v4_relat_1(X1,X0) | ~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v1_relat_1(X1)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f60])).
% 0.21/0.52  fof(f60,plain,(
% 0.21/0.52    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(nnf_transformation,[],[f46])).
% 0.21/0.52  fof(f46,plain,(
% 0.21/0.52    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 0.21/0.52    inference(flattening,[],[f45])).
% 0.21/0.52  fof(f45,plain,(
% 0.21/0.52    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 0.21/0.52    inference(ennf_transformation,[],[f16])).
% 0.21/0.52  fof(f16,axiom,(
% 0.21/0.52    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 0.21/0.52  fof(f91,plain,(
% 0.21/0.52    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 0.21/0.52    inference(cnf_transformation,[],[f47])).
% 0.21/0.52  fof(f47,plain,(
% 0.21/0.52    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.52    inference(ennf_transformation,[],[f10])).
% 0.21/0.52  fof(f10,axiom,(
% 0.21/0.52    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.52  fof(f283,plain,(
% 0.21/0.52    ~spl3_32 | spl3_17 | ~spl3_26),
% 0.21/0.52    inference(avatar_split_clause,[],[f266,f250,f180,f281])).
% 0.21/0.52  fof(f180,plain,(
% 0.21/0.52    spl3_17 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.52  fof(f266,plain,(
% 0.21/0.52    ~v1_xboole_0(k2_relat_1(sK2)) | (spl3_17 | ~spl3_26)),
% 0.21/0.52    inference(superposition,[],[f181,f251])).
% 0.21/0.52  fof(f181,plain,(
% 0.21/0.52    ~v1_xboole_0(k2_struct_0(sK1)) | spl3_17),
% 0.21/0.52    inference(avatar_component_clause,[],[f180])).
% 0.21/0.52  fof(f279,plain,(
% 0.21/0.52    spl3_31 | ~spl3_16 | ~spl3_26),
% 0.21/0.52    inference(avatar_split_clause,[],[f265,f250,f174,f277])).
% 0.21/0.52  fof(f174,plain,(
% 0.21/0.52    spl3_16 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.52  fof(f265,plain,(
% 0.21/0.52    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_16 | ~spl3_26)),
% 0.21/0.52    inference(superposition,[],[f175,f251])).
% 0.21/0.52  fof(f175,plain,(
% 0.21/0.52    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_16),
% 0.21/0.52    inference(avatar_component_clause,[],[f174])).
% 0.21/0.52  fof(f275,plain,(
% 0.21/0.52    spl3_30 | ~spl3_15 | ~spl3_26),
% 0.21/0.52    inference(avatar_split_clause,[],[f264,f250,f169,f273])).
% 0.21/0.52  fof(f264,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_15 | ~spl3_26)),
% 0.21/0.52    inference(superposition,[],[f170,f251])).
% 0.21/0.52  fof(f261,plain,(
% 0.21/0.52    spl3_26 | ~spl3_13 | ~spl3_25),
% 0.21/0.52    inference(avatar_split_clause,[],[f259,f246,f153,f250])).
% 0.21/0.52  fof(f246,plain,(
% 0.21/0.52    spl3_25 <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.52  fof(f259,plain,(
% 0.21/0.52    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_13 | ~spl3_25)),
% 0.21/0.52    inference(superposition,[],[f154,f247])).
% 0.21/0.52  fof(f247,plain,(
% 0.21/0.52    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_25),
% 0.21/0.52    inference(avatar_component_clause,[],[f246])).
% 0.21/0.52  fof(f248,plain,(
% 0.21/0.52    spl3_25 | ~spl3_15),
% 0.21/0.52    inference(avatar_split_clause,[],[f244,f169,f246])).
% 0.21/0.52  fof(f244,plain,(
% 0.21/0.52    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_15),
% 0.21/0.52    inference(resolution,[],[f92,f170])).
% 0.21/0.52  fof(f223,plain,(
% 0.21/0.52    spl3_15 | ~spl3_5 | ~spl3_11 | ~spl3_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f222,f149,f145,f118,f169])).
% 0.21/0.52  fof(f118,plain,(
% 0.21/0.52    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.52  fof(f145,plain,(
% 0.21/0.52    spl3_11 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.52  fof(f149,plain,(
% 0.21/0.52    spl3_12 <=> k2_struct_0(sK0) = u1_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.52  fof(f222,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_5 | ~spl3_11 | ~spl3_12)),
% 0.21/0.52    inference(forward_demodulation,[],[f221,f150])).
% 0.21/0.52  fof(f150,plain,(
% 0.21/0.52    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_12),
% 0.21/0.52    inference(avatar_component_clause,[],[f149])).
% 0.21/0.52  fof(f221,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_5 | ~spl3_11)),
% 0.21/0.52    inference(forward_demodulation,[],[f119,f146])).
% 0.21/0.52  fof(f146,plain,(
% 0.21/0.52    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_11),
% 0.21/0.52    inference(avatar_component_clause,[],[f145])).
% 0.21/0.52  fof(f119,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_5),
% 0.21/0.52    inference(avatar_component_clause,[],[f118])).
% 0.21/0.52  fof(f219,plain,(
% 0.21/0.52    ~spl3_5 | spl3_20),
% 0.21/0.52    inference(avatar_contradiction_clause,[],[f217])).
% 0.21/0.52  fof(f217,plain,(
% 0.21/0.52    $false | (~spl3_5 | spl3_20)),
% 0.21/0.52    inference(subsumption_resolution,[],[f119,f216])).
% 0.21/0.52  fof(f216,plain,(
% 0.21/0.52    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_20),
% 0.21/0.52    inference(resolution,[],[f209,f91])).
% 0.21/0.52  fof(f209,plain,(
% 0.21/0.52    ~v1_relat_1(sK2) | spl3_20),
% 0.21/0.52    inference(avatar_component_clause,[],[f208])).
% 0.21/0.52  fof(f214,plain,(
% 0.21/0.52    ~spl3_20 | ~spl3_7 | spl3_21 | ~spl3_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f205,f110,f212,f126,f208])).
% 0.21/0.52  fof(f205,plain,(
% 0.21/0.52    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_3),
% 0.21/0.52    inference(resolution,[],[f81,f111])).
% 0.21/0.52  fof(f81,plain,(
% 0.21/0.52    ( ! [X0] : (~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f36])).
% 0.21/0.52  fof(f36,plain,(
% 0.21/0.52    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.52    inference(flattening,[],[f35])).
% 0.21/0.52  fof(f35,plain,(
% 0.21/0.52    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f9])).
% 0.21/0.52  fof(f9,axiom,(
% 0.21/0.52    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.21/0.52  fof(f182,plain,(
% 0.21/0.52    spl3_9 | ~spl3_8 | ~spl3_17 | ~spl3_11),
% 0.21/0.52    inference(avatar_split_clause,[],[f159,f145,f180,f130,f134])).
% 0.21/0.52  fof(f134,plain,(
% 0.21/0.52    spl3_9 <=> v2_struct_0(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.52  fof(f130,plain,(
% 0.21/0.52    spl3_8 <=> l1_struct_0(sK1)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.52  fof(f159,plain,(
% 0.21/0.52    ~v1_xboole_0(k2_struct_0(sK1)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_11),
% 0.21/0.52    inference(superposition,[],[f75,f146])).
% 0.21/0.52  fof(f75,plain,(
% 0.21/0.52    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f30])).
% 0.21/0.52  fof(f30,plain,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f29])).
% 0.21/0.52  fof(f29,plain,(
% 0.21/0.52    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.52    inference(ennf_transformation,[],[f19])).
% 0.21/0.52  fof(f19,axiom,(
% 0.21/0.52    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.52  fof(f176,plain,(
% 0.21/0.52    spl3_16 | ~spl3_6 | ~spl3_11 | ~spl3_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f172,f149,f145,f122,f174])).
% 0.21/0.52  fof(f122,plain,(
% 0.21/0.52    spl3_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.52  fof(f172,plain,(
% 0.21/0.52    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_6 | ~spl3_11 | ~spl3_12)),
% 0.21/0.52    inference(forward_demodulation,[],[f158,f150])).
% 0.21/0.52  fof(f158,plain,(
% 0.21/0.52    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_6 | ~spl3_11)),
% 0.21/0.52    inference(superposition,[],[f123,f146])).
% 0.21/0.52  fof(f123,plain,(
% 0.21/0.52    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_6),
% 0.21/0.52    inference(avatar_component_clause,[],[f122])).
% 0.21/0.52  fof(f166,plain,(
% 0.21/0.52    spl3_13 | ~spl3_4 | ~spl3_11 | ~spl3_12),
% 0.21/0.52    inference(avatar_split_clause,[],[f165,f149,f145,f114,f153])).
% 0.21/0.52  fof(f114,plain,(
% 0.21/0.52    spl3_4 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.52  fof(f165,plain,(
% 0.21/0.52    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_11 | ~spl3_12)),
% 0.21/0.52    inference(forward_demodulation,[],[f156,f150])).
% 0.21/0.52  fof(f156,plain,(
% 0.21/0.52    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_11)),
% 0.21/0.52    inference(superposition,[],[f115,f146])).
% 0.21/0.52  fof(f115,plain,(
% 0.21/0.52    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_4),
% 0.21/0.52    inference(avatar_component_clause,[],[f114])).
% 0.21/0.52  fof(f151,plain,(
% 0.21/0.52    spl3_12 | ~spl3_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f143,f138,f149])).
% 0.21/0.52  fof(f138,plain,(
% 0.21/0.52    spl3_10 <=> l1_struct_0(sK0)),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.52  fof(f143,plain,(
% 0.21/0.52    k2_struct_0(sK0) = u1_struct_0(sK0) | ~spl3_10),
% 0.21/0.52    inference(resolution,[],[f72,f139])).
% 0.21/0.52  fof(f139,plain,(
% 0.21/0.52    l1_struct_0(sK0) | ~spl3_10),
% 0.21/0.52    inference(avatar_component_clause,[],[f138])).
% 0.21/0.52  fof(f72,plain,(
% 0.21/0.52    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.52    inference(cnf_transformation,[],[f26])).
% 0.21/0.52  fof(f26,plain,(
% 0.21/0.52    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f18])).
% 0.21/0.52  fof(f18,axiom,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.52  fof(f147,plain,(
% 0.21/0.52    spl3_11 | ~spl3_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f142,f130,f145])).
% 0.21/0.52  fof(f142,plain,(
% 0.21/0.52    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_8),
% 0.21/0.52    inference(resolution,[],[f72,f131])).
% 0.21/0.52  fof(f131,plain,(
% 0.21/0.52    l1_struct_0(sK1) | ~spl3_8),
% 0.21/0.52    inference(avatar_component_clause,[],[f130])).
% 0.21/0.52  fof(f140,plain,(
% 0.21/0.52    spl3_10),
% 0.21/0.52    inference(avatar_split_clause,[],[f61,f138])).
% 0.21/0.52  fof(f61,plain,(
% 0.21/0.52    l1_struct_0(sK0)),
% 0.21/0.52    inference(cnf_transformation,[],[f59])).
% 0.21/0.52  fof(f59,plain,(
% 0.21/0.52    (((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.21/0.52    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f25,f58,f57,f56])).
% 0.21/0.52  % (16461)lrs+4_2_av=off:gs=on:gsem=on:lma=on:nm=16:nwc=1:sas=z3:stl=30:sos=on:urr=on_159 on theBenchmark
% 0.21/0.52  fof(f56,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f57,plain,(
% 0.21/0.52    ? [X1] : (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f58,plain,(
% 0.21/0.52    ? [X2] : ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => ((k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.21/0.52    introduced(choice_axiom,[])).
% 0.21/0.52  fof(f25,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : ((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.52    inference(flattening,[],[f24])).
% 0.21/0.52  % (16465)dis+11_3_add=off:afr=on:afp=40000:afq=2.0:amm=sco:anc=none:cond=on:nm=16:nwc=1:ss=axioms:st=5.0:sos=all:sp=reverse_arity_169 on theBenchmark
% 0.21/0.52  fof(f24,plain,(
% 0.21/0.52    ? [X0] : (? [X1] : (? [X2] : (((k2_struct_0(X0) != k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) | k2_struct_0(X1) != k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.21/0.52    inference(ennf_transformation,[],[f22])).
% 0.21/0.52  fof(f22,negated_conjecture,(
% 0.21/0.52    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.21/0.52    inference(negated_conjecture,[],[f21])).
% 0.21/0.52  fof(f21,conjecture,(
% 0.21/0.52    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k2_struct_0(X0) = k2_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) & k2_struct_0(X1) = k1_relset_1(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.21/0.52    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_tops_2)).
% 0.21/0.52  fof(f136,plain,(
% 0.21/0.52    ~spl3_9),
% 0.21/0.52    inference(avatar_split_clause,[],[f62,f134])).
% 0.21/0.52  fof(f62,plain,(
% 0.21/0.52    ~v2_struct_0(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f59])).
% 0.21/0.52  fof(f132,plain,(
% 0.21/0.52    spl3_8),
% 0.21/0.52    inference(avatar_split_clause,[],[f63,f130])).
% 0.21/0.52  fof(f63,plain,(
% 0.21/0.52    l1_struct_0(sK1)),
% 0.21/0.52    inference(cnf_transformation,[],[f59])).
% 0.21/0.52  fof(f128,plain,(
% 0.21/0.52    spl3_7),
% 0.21/0.52    inference(avatar_split_clause,[],[f64,f126])).
% 0.21/0.52  fof(f64,plain,(
% 0.21/0.52    v1_funct_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f59])).
% 0.21/0.52  fof(f124,plain,(
% 0.21/0.52    spl3_6),
% 0.21/0.52    inference(avatar_split_clause,[],[f65,f122])).
% 0.21/0.52  fof(f65,plain,(
% 0.21/0.52    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.52    inference(cnf_transformation,[],[f59])).
% 0.21/0.52  fof(f120,plain,(
% 0.21/0.52    spl3_5),
% 0.21/0.52    inference(avatar_split_clause,[],[f66,f118])).
% 0.21/0.52  fof(f66,plain,(
% 0.21/0.52    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.52    inference(cnf_transformation,[],[f59])).
% 0.21/0.52  fof(f116,plain,(
% 0.21/0.52    spl3_4),
% 0.21/0.52    inference(avatar_split_clause,[],[f67,f114])).
% 0.21/0.52  fof(f67,plain,(
% 0.21/0.52    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f59])).
% 0.21/0.52  fof(f112,plain,(
% 0.21/0.52    spl3_3),
% 0.21/0.52    inference(avatar_split_clause,[],[f68,f110])).
% 0.21/0.52  fof(f68,plain,(
% 0.21/0.52    v2_funct_1(sK2)),
% 0.21/0.52    inference(cnf_transformation,[],[f59])).
% 0.21/0.52  fof(f108,plain,(
% 0.21/0.52    ~spl3_1 | ~spl3_2),
% 0.21/0.52    inference(avatar_split_clause,[],[f69,f106,f103])).
% 0.21/0.52  fof(f103,plain,(
% 0.21/0.52    spl3_1 <=> k2_struct_0(sK1) = k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.52  fof(f106,plain,(
% 0.21/0.52    spl3_2 <=> k2_struct_0(sK0) = k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.52    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.52  fof(f69,plain,(
% 0.21/0.52    k2_struct_0(sK0) != k2_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k2_struct_0(sK1) != k1_relset_1(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.52    inference(cnf_transformation,[],[f59])).
% 0.21/0.52  % SZS output end Proof for theBenchmark
% 0.21/0.52  % (16452)------------------------------
% 0.21/0.52  % (16452)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.52  % (16452)Termination reason: Refutation
% 0.21/0.52  
% 0.21/0.52  % (16452)Memory used [KB]: 11257
% 0.21/0.52  % (16452)Time elapsed: 0.105 s
% 0.21/0.52  % (16452)------------------------------
% 0.21/0.52  % (16452)------------------------------
% 0.21/0.52  % (16445)Success in time 0.164 s
%------------------------------------------------------------------------------
