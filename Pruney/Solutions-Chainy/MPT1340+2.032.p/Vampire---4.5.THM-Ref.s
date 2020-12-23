%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:21 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  263 ( 572 expanded)
%              Number of leaves         :   60 ( 261 expanded)
%              Depth                    :    9
%              Number of atoms          :  962 (2259 expanded)
%              Number of equality atoms :  167 ( 368 expanded)
%              Maximal formula depth    :   13 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f530,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f86,f91,f96,f101,f106,f111,f116,f124,f129,f134,f146,f151,f166,f174,f179,f187,f205,f217,f236,f241,f247,f259,f264,f269,f291,f292,f306,f316,f333,f338,f352,f359,f385,f395,f399,f403,f415,f441,f450,f481,f506,f518,f529])).

fof(f529,plain,
    ( ~ spl3_41
    | ~ spl3_45
    | ~ spl3_49
    | spl3_52
    | ~ spl3_54
    | ~ spl3_59 ),
    inference(avatar_contradiction_clause,[],[f528])).

fof(f528,plain,
    ( $false
    | ~ spl3_41
    | ~ spl3_45
    | ~ spl3_49
    | spl3_52
    | ~ spl3_54
    | ~ spl3_59 ),
    inference(subsumption_resolution,[],[f522,f358])).

fof(f358,plain,
    ( r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | ~ spl3_41 ),
    inference(avatar_component_clause,[],[f356])).

fof(f356,plain,
    ( spl3_41
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).

fof(f522,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | ~ spl3_45
    | ~ spl3_49
    | spl3_52
    | ~ spl3_54
    | ~ spl3_59 ),
    inference(backward_demodulation,[],[f440,f521])).

fof(f521,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_45
    | ~ spl3_49
    | ~ spl3_54
    | ~ spl3_59 ),
    inference(subsumption_resolution,[],[f520,f394])).

fof(f394,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_45 ),
    inference(avatar_component_clause,[],[f392])).

fof(f392,plain,
    ( spl3_45
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).

fof(f520,plain,
    ( sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_49
    | ~ spl3_54
    | ~ spl3_59 ),
    inference(subsumption_resolution,[],[f519,f480])).

fof(f480,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_54 ),
    inference(avatar_component_clause,[],[f478])).

fof(f478,plain,
    ( spl3_54
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).

fof(f519,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_49
    | ~ spl3_59 ),
    inference(resolution,[],[f517,f414])).

fof(f414,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_49 ),
    inference(avatar_component_clause,[],[f412])).

fof(f412,plain,
    ( spl3_49
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).

fof(f517,plain,
    ( ! [X6,X7] :
        ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | k2_relset_1(X6,X7,k2_funct_1(sK2)) != X7
        | sK2 = k2_tops_2(X6,X7,k2_funct_1(sK2))
        | ~ v1_funct_2(k2_funct_1(sK2),X6,X7) )
    | ~ spl3_59 ),
    inference(avatar_component_clause,[],[f516])).

fof(f516,plain,
    ( spl3_59
  <=> ! [X7,X6] :
        ( sK2 = k2_tops_2(X6,X7,k2_funct_1(sK2))
        | k2_relset_1(X6,X7,k2_funct_1(sK2)) != X7
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_funct_2(k2_funct_1(sK2),X6,X7) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).

fof(f440,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)
    | spl3_52 ),
    inference(avatar_component_clause,[],[f438])).

fof(f438,plain,
    ( spl3_52
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).

fof(f518,plain,
    ( spl3_59
    | ~ spl3_18
    | ~ spl3_42
    | ~ spl3_56 ),
    inference(avatar_split_clause,[],[f514,f493,f361,f184,f516])).

fof(f184,plain,
    ( spl3_18
  <=> sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f361,plain,
    ( spl3_42
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).

fof(f493,plain,
    ( spl3_56
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).

fof(f514,plain,
    ( ! [X6,X7] :
        ( sK2 = k2_tops_2(X6,X7,k2_funct_1(sK2))
        | k2_relset_1(X6,X7,k2_funct_1(sK2)) != X7
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_funct_2(k2_funct_1(sK2),X6,X7) )
    | ~ spl3_18
    | ~ spl3_42
    | ~ spl3_56 ),
    inference(subsumption_resolution,[],[f467,f494])).

fof(f494,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_56 ),
    inference(avatar_component_clause,[],[f493])).

fof(f467,plain,
    ( ! [X6,X7] :
        ( sK2 = k2_tops_2(X6,X7,k2_funct_1(sK2))
        | ~ v2_funct_1(k2_funct_1(sK2))
        | k2_relset_1(X6,X7,k2_funct_1(sK2)) != X7
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_funct_2(k2_funct_1(sK2),X6,X7) )
    | ~ spl3_18
    | ~ spl3_42 ),
    inference(forward_demodulation,[],[f457,f186])).

fof(f186,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f184])).

fof(f457,plain,
    ( ! [X6,X7] :
        ( ~ v2_funct_1(k2_funct_1(sK2))
        | k2_relset_1(X6,X7,k2_funct_1(sK2)) != X7
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X6,X7)))
        | ~ v1_funct_2(k2_funct_1(sK2),X6,X7)
        | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X6,X7,k2_funct_1(sK2)) )
    | ~ spl3_42 ),
    inference(resolution,[],[f363,f72])).

fof(f72,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ),
    inference(cnf_transformation,[],[f35])).

fof(f35,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f34])).

fof(f34,plain,(
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

fof(f363,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_42 ),
    inference(avatar_component_clause,[],[f361])).

fof(f506,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | ~ spl3_16
    | spl3_56 ),
    inference(avatar_contradiction_clause,[],[f505])).

fof(f505,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_16
    | spl3_56 ),
    inference(subsumption_resolution,[],[f504,f173])).

fof(f173,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f171])).

fof(f171,plain,
    ( spl3_16
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f504,plain,
    ( ~ v1_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_5
    | spl3_56 ),
    inference(subsumption_resolution,[],[f503,f100])).

fof(f100,plain,
    ( v1_funct_1(sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f98])).

fof(f98,plain,
    ( spl3_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f503,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_5
    | spl3_56 ),
    inference(subsumption_resolution,[],[f501,f105])).

fof(f105,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f103])).

fof(f103,plain,
    ( spl3_5
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f501,plain,
    ( ~ v2_funct_1(sK2)
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_56 ),
    inference(resolution,[],[f495,f56])).

fof(f56,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f22])).

fof(f22,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f21])).

fof(f21,plain,(
    ! [X0] :
      ( v2_funct_1(k2_funct_1(X0))
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => v2_funct_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).

fof(f495,plain,
    ( ~ v2_funct_1(k2_funct_1(sK2))
    | spl3_56 ),
    inference(avatar_component_clause,[],[f493])).

fof(f481,plain,
    ( spl3_54
    | ~ spl3_20
    | ~ spl3_49 ),
    inference(avatar_split_clause,[],[f424,f412,f202,f478])).

fof(f202,plain,
    ( spl3_20
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f424,plain,
    ( k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_20
    | ~ spl3_49 ),
    inference(forward_demodulation,[],[f420,f204])).

fof(f204,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f202])).

fof(f420,plain,
    ( k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | ~ spl3_49 ),
    inference(resolution,[],[f414,f62])).

fof(f62,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f450,plain,
    ( ~ spl3_4
    | ~ spl3_5
    | ~ spl3_33
    | ~ spl3_35
    | ~ spl3_38
    | spl3_42 ),
    inference(avatar_contradiction_clause,[],[f449])).

fof(f449,plain,
    ( $false
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_33
    | ~ spl3_35
    | ~ spl3_38
    | spl3_42 ),
    inference(unit_resulting_resolution,[],[f100,f105,f305,f315,f337,f362,f69])).

fof(f69,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | v1_funct_1(k2_funct_1(X2)) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f33,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f32])).

fof(f32,plain,(
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
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_42 ),
    inference(avatar_component_clause,[],[f361])).

fof(f337,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_38 ),
    inference(avatar_component_clause,[],[f335])).

fof(f335,plain,
    ( spl3_38
  <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).

fof(f315,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f313])).

fof(f313,plain,
    ( spl3_35
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f305,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f303])).

fof(f303,plain,
    ( spl3_33
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f441,plain,
    ( ~ spl3_52
    | ~ spl3_33
    | ~ spl3_35
    | spl3_37
    | ~ spl3_38
    | ~ spl3_47 ),
    inference(avatar_split_clause,[],[f426,f401,f335,f330,f313,f303,f438])).

fof(f330,plain,
    ( spl3_37
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).

fof(f401,plain,
    ( spl3_47
  <=> ! [X1,X0] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f426,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)
    | ~ spl3_33
    | ~ spl3_35
    | spl3_37
    | ~ spl3_38
    | ~ spl3_47 ),
    inference(backward_demodulation,[],[f332,f418])).

fof(f418,plain,
    ( k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_33
    | ~ spl3_35
    | ~ spl3_38
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f417,f305])).

fof(f417,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_35
    | ~ spl3_38
    | ~ spl3_47 ),
    inference(subsumption_resolution,[],[f416,f337])).

fof(f416,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_35
    | ~ spl3_47 ),
    inference(resolution,[],[f402,f315])).

fof(f402,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) )
    | ~ spl3_47 ),
    inference(avatar_component_clause,[],[f401])).

fof(f332,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)
    | spl3_37 ),
    inference(avatar_component_clause,[],[f330])).

fof(f415,plain,
    ( spl3_49
    | ~ spl3_33
    | ~ spl3_35
    | ~ spl3_38
    | ~ spl3_46 ),
    inference(avatar_split_clause,[],[f410,f397,f335,f313,f303,f412])).

fof(f397,plain,
    ( spl3_46
  <=> ! [X1,X0] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f410,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_33
    | ~ spl3_35
    | ~ spl3_38
    | ~ spl3_46 ),
    inference(subsumption_resolution,[],[f409,f305])).

fof(f409,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_35
    | ~ spl3_38
    | ~ spl3_46 ),
    inference(subsumption_resolution,[],[f408,f337])).

fof(f408,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_35
    | ~ spl3_46 ),
    inference(resolution,[],[f398,f315])).

fof(f398,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1
        | ~ v1_funct_2(sK2,X0,X1)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl3_46 ),
    inference(avatar_component_clause,[],[f397])).

fof(f403,plain,
    ( spl3_47
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f294,f103,f98,f401])).

fof(f294,plain,
    ( ! [X0,X1] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) )
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f293,f105])).

fof(f293,plain,
    ( ! [X0,X1] :
        ( ~ v2_funct_1(sK2)
        | k2_relset_1(X0,X1,sK2) != X1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) )
    | ~ spl3_4 ),
    inference(resolution,[],[f72,f100])).

fof(f399,plain,
    ( spl3_46
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f282,f103,f98,f397])).

fof(f282,plain,
    ( ! [X0,X1] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f281,f105])).

fof(f281,plain,
    ( ! [X0,X1] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | ~ v2_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) )
    | ~ spl3_4 ),
    inference(resolution,[],[f71,f100])).

fof(f71,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f395,plain,
    ( spl3_45
    | ~ spl3_33
    | ~ spl3_35
    | ~ spl3_38
    | ~ spl3_44 ),
    inference(avatar_split_clause,[],[f390,f383,f335,f313,f303,f392])).

fof(f383,plain,
    ( spl3_44
  <=> ! [X1,X0] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_funct_2(k2_funct_1(sK2),X1,X0) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).

fof(f390,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_33
    | ~ spl3_35
    | ~ spl3_38
    | ~ spl3_44 ),
    inference(subsumption_resolution,[],[f389,f305])).

fof(f389,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_35
    | ~ spl3_38
    | ~ spl3_44 ),
    inference(subsumption_resolution,[],[f388,f337])).

fof(f388,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ spl3_35
    | ~ spl3_44 ),
    inference(resolution,[],[f384,f315])).

fof(f384,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_funct_2(k2_funct_1(sK2),X1,X0) )
    | ~ spl3_44 ),
    inference(avatar_component_clause,[],[f383])).

fof(f385,plain,
    ( spl3_44
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(avatar_split_clause,[],[f279,f103,f98,f383])).

fof(f279,plain,
    ( ! [X0,X1] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_funct_2(k2_funct_1(sK2),X1,X0) )
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f278,f105])).

fof(f278,plain,
    ( ! [X0,X1] :
        ( k2_relset_1(X0,X1,sK2) != X1
        | ~ v2_funct_1(sK2)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | v1_funct_2(k2_funct_1(sK2),X1,X0) )
    | ~ spl3_4 ),
    inference(resolution,[],[f70,f100])).

fof(f70,plain,(
    ! [X2,X0,X1] :
      ( ~ v1_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | v1_funct_2(k2_funct_1(X2),X1,X0) ) ),
    inference(cnf_transformation,[],[f33])).

fof(f359,plain,
    ( spl3_41
    | ~ spl3_33
    | ~ spl3_35
    | ~ spl3_40 ),
    inference(avatar_split_clause,[],[f354,f350,f313,f303,f356])).

fof(f350,plain,
    ( spl3_40
  <=> ! [X1,X0] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | r2_funct_2(X0,X1,sK2,sK2) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).

fof(f354,plain,
    ( r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | ~ spl3_33
    | ~ spl3_35
    | ~ spl3_40 ),
    inference(subsumption_resolution,[],[f353,f305])).

fof(f353,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | ~ spl3_35
    | ~ spl3_40 ),
    inference(resolution,[],[f351,f315])).

fof(f351,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | r2_funct_2(X0,X1,sK2,sK2) )
    | ~ spl3_40 ),
    inference(avatar_component_clause,[],[f350])).

fof(f352,plain,
    ( spl3_40
    | ~ spl3_4 ),
    inference(avatar_split_clause,[],[f270,f98,f350])).

fof(f270,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_2(sK2,X0,X1)
        | r2_funct_2(X0,X1,sK2,sK2) )
    | ~ spl3_4 ),
    inference(resolution,[],[f81,f100])).

fof(f81,plain,(
    ! [X0,X3,X1] :
      ( ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | r2_funct_2(X0,X1,X3,X3) ) ),
    inference(duplicate_literal_removal,[],[f80])).

fof(f80,plain,(
    ! [X0,X3,X1] :
      ( r2_funct_2(X0,X1,X3,X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3) ) ),
    inference(equality_resolution,[],[f74])).

fof(f74,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X3)
      | X2 != X3
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f43])).

fof(f43,plain,(
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
    inference(nnf_transformation,[],[f37])).

fof(f37,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f36])).

fof(f36,plain,(
    ! [X0,X1,X2,X3] :
      ( ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 )
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
     => ( r2_funct_2(X0,X1,X2,X3)
      <=> X2 = X3 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).

fof(f338,plain,
    ( spl3_38
    | ~ spl3_29
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f300,f288,f261,f335])).

fof(f261,plain,
    ( spl3_29
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f288,plain,
    ( spl3_32
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).

fof(f300,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_29
    | ~ spl3_32 ),
    inference(backward_demodulation,[],[f263,f290])).

fof(f290,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_32 ),
    inference(avatar_component_clause,[],[f288])).

fof(f263,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f261])).

fof(f333,plain,
    ( ~ spl3_37
    | spl3_28
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f299,f288,f256,f330])).

fof(f256,plain,
    ( spl3_28
  <=> r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f299,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)
    | spl3_28
    | ~ spl3_32 ),
    inference(backward_demodulation,[],[f258,f290])).

fof(f258,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)
    | spl3_28 ),
    inference(avatar_component_clause,[],[f256])).

fof(f316,plain,
    ( spl3_35
    | ~ spl3_27
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f298,f288,f244,f313])).

fof(f244,plain,
    ( spl3_27
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f298,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_27
    | ~ spl3_32 ),
    inference(backward_demodulation,[],[f246,f290])).

fof(f246,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f244])).

fof(f306,plain,
    ( spl3_33
    | ~ spl3_25
    | ~ spl3_32 ),
    inference(avatar_split_clause,[],[f297,f288,f233,f303])).

fof(f233,plain,
    ( spl3_25
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f297,plain,
    ( v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ spl3_25
    | ~ spl3_32 ),
    inference(backward_demodulation,[],[f235,f290])).

fof(f235,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f233])).

fof(f292,plain,
    ( k1_xboole_0 != k2_relat_1(sK2)
    | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2)
    | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | v1_xboole_0(k2_struct_0(sK1))
    | ~ v1_xboole_0(k1_xboole_0) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f291,plain,
    ( spl3_31
    | spl3_32
    | ~ spl3_25
    | ~ spl3_27
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f280,f266,f244,f233,f288,f284])).

fof(f284,plain,
    ( spl3_31
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).

fof(f266,plain,
    ( spl3_30
  <=> k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f280,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl3_25
    | ~ spl3_27
    | ~ spl3_30 ),
    inference(forward_demodulation,[],[f273,f268])).

fof(f268,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f266])).

fof(f273,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_25
    | ~ spl3_27 ),
    inference(subsumption_resolution,[],[f272,f235])).

fof(f272,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2)
    | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_27 ),
    inference(resolution,[],[f63,f246])).

fof(f63,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | k1_xboole_0 = X1
      | k1_relset_1(X0,X1,X2) = X0 ) ),
    inference(cnf_transformation,[],[f42])).

fof(f42,plain,(
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
    inference(nnf_transformation,[],[f31])).

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
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
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

fof(f269,plain,
    ( spl3_30
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f249,f244,f266])).

fof(f249,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_27 ),
    inference(resolution,[],[f246,f61])).

fof(f61,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f264,plain,
    ( spl3_29
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f248,f244,f261])).

fof(f248,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_27 ),
    inference(resolution,[],[f246,f62])).

fof(f259,plain,
    ( ~ spl3_28
    | ~ spl3_8
    | ~ spl3_26 ),
    inference(avatar_split_clause,[],[f253,f238,f121,f256])).

fof(f121,plain,
    ( spl3_8
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f238,plain,
    ( spl3_26
  <=> u1_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f253,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)
    | ~ spl3_8
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f252,f123])).

fof(f123,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f121])).

fof(f252,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)
    | ~ spl3_26 ),
    inference(forward_demodulation,[],[f52,f240])).

fof(f240,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_26 ),
    inference(avatar_component_clause,[],[f238])).

fof(f52,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f40,f39,f38])).

fof(f38,plain,
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

fof(f39,plain,
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

fof(f40,plain,
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

fof(f17,plain,(
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
    inference(flattening,[],[f16])).

fof(f16,plain,(
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
                 => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
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
               => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).

fof(f247,plain,
    ( spl3_27
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f218,f176,f163,f244])).

fof(f163,plain,
    ( spl3_15
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f176,plain,
    ( spl3_17
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f218,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(backward_demodulation,[],[f165,f212])).

fof(f212,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(backward_demodulation,[],[f178,f206])).

fof(f206,plain,
    ( k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)
    | ~ spl3_15 ),
    inference(resolution,[],[f62,f165])).

fof(f178,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_17 ),
    inference(avatar_component_clause,[],[f176])).

fof(f165,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f163])).

fof(f241,plain,
    ( spl3_26
    | ~ spl3_10
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f221,f176,f163,f131,f238])).

fof(f131,plain,
    ( spl3_10
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f221,plain,
    ( u1_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_10
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(backward_demodulation,[],[f133,f212])).

fof(f133,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_10 ),
    inference(avatar_component_clause,[],[f131])).

fof(f236,plain,
    ( spl3_25
    | ~ spl3_11
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(avatar_split_clause,[],[f220,f176,f163,f143,f233])).

fof(f143,plain,
    ( spl3_11
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f220,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_11
    | ~ spl3_15
    | ~ spl3_17 ),
    inference(backward_demodulation,[],[f145,f212])).

fof(f145,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f143])).

fof(f217,plain,
    ( spl3_22
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f206,f163,f214])).

fof(f214,plain,
    ( spl3_22
  <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f205,plain,
    ( spl3_20
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f194,f171,f103,f98,f202])).

fof(f194,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f193,f173])).

fof(f193,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f192,f105])).

fof(f192,plain,
    ( ~ v2_funct_1(sK2)
    | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f59,f100])).

fof(f59,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
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

fof(f187,plain,
    ( spl3_18
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f182,f171,f103,f98,f184])).

fof(f182,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_4
    | ~ spl3_5
    | ~ spl3_16 ),
    inference(subsumption_resolution,[],[f181,f173])).

fof(f181,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_4
    | ~ spl3_5 ),
    inference(subsumption_resolution,[],[f180,f105])).

% (9591)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
fof(f180,plain,
    ( ~ v2_funct_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ spl3_4 ),
    inference(resolution,[],[f57,f100])).

fof(f57,plain,(
    ! [X0] :
      ( ~ v1_funct_1(X0)
      | ~ v2_funct_1(X0)
      | k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k2_funct_1(k2_funct_1(X0)) = X0
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f23])).

fof(f23,plain,(
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

fof(f179,plain,
    ( spl3_17
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f169,f131,f121,f176])).

fof(f169,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f168,f123])).

fof(f168,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f50,f133])).

fof(f50,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f174,plain,
    ( spl3_16
    | ~ spl3_15 ),
    inference(avatar_split_clause,[],[f167,f163,f171])).

fof(f167,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_15 ),
    inference(resolution,[],[f60,f165])).

fof(f60,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f27])).

fof(f27,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f166,plain,
    ( spl3_15
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f152,f131,f121,f163])).

fof(f152,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_8
    | ~ spl3_10 ),
    inference(forward_demodulation,[],[f137,f133])).

fof(f137,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_8 ),
    inference(forward_demodulation,[],[f49,f123])).

fof(f49,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f41])).

fof(f151,plain,
    ( ~ spl3_12
    | spl3_2
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f141,f131,f93,f88,f148])).

fof(f148,plain,
    ( spl3_12
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f88,plain,
    ( spl3_2
  <=> v2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f93,plain,
    ( spl3_3
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f141,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_2
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f140,f90])).

fof(f90,plain,
    ( ~ v2_struct_0(sK1)
    | spl3_2 ),
    inference(avatar_component_clause,[],[f88])).

fof(f140,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | v2_struct_0(sK1)
    | ~ spl3_3
    | ~ spl3_10 ),
    inference(subsumption_resolution,[],[f139,f95])).

fof(f95,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f93])).

fof(f139,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK1)
    | v2_struct_0(sK1)
    | ~ spl3_10 ),
    inference(superposition,[],[f55,f133])).

fof(f55,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f20])).

fof(f20,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f19])).

fof(f19,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).

fof(f146,plain,
    ( spl3_11
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(avatar_split_clause,[],[f138,f131,f126,f143])).

fof(f126,plain,
    ( spl3_9
  <=> v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f138,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_9
    | ~ spl3_10 ),
    inference(backward_demodulation,[],[f128,f133])).

fof(f128,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f126])).

fof(f134,plain,
    ( spl3_10
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f118,f93,f131])).

fof(f118,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_3 ),
    inference(resolution,[],[f54,f95])).

fof(f54,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f129,plain,
    ( spl3_9
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(avatar_split_clause,[],[f119,f113,f83,f126])).

fof(f83,plain,
    ( spl3_1
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f113,plain,
    ( spl3_7
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f119,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_1
    | ~ spl3_7 ),
    inference(backward_demodulation,[],[f115,f117])).

fof(f117,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_1 ),
    inference(resolution,[],[f54,f85])).

fof(f85,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_1 ),
    inference(avatar_component_clause,[],[f83])).

fof(f115,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_7 ),
    inference(avatar_component_clause,[],[f113])).

fof(f124,plain,
    ( spl3_8
    | ~ spl3_1 ),
    inference(avatar_split_clause,[],[f117,f83,f121])).

fof(f116,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f48,f113])).

fof(f48,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f41])).

fof(f111,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f53,f108])).

fof(f108,plain,
    ( spl3_6
  <=> v1_xboole_0(k1_xboole_0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f53,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f106,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f51,f103])).

fof(f51,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f101,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f47,f98])).

fof(f47,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f41])).

fof(f96,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f46,f93])).

fof(f46,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f91,plain,(
    ~ spl3_2 ),
    inference(avatar_split_clause,[],[f45,f88])).

fof(f45,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f41])).

fof(f86,plain,(
    spl3_1 ),
    inference(avatar_split_clause,[],[f44,f83])).

fof(f44,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : run_vampire %s %d
% 0.15/0.35  % Computer   : n002.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % WCLimit    : 600
% 0.15/0.35  % DateTime   : Tue Dec  1 10:59:52 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.21/0.47  % (9582)dis+11_1_acc=on:afp=1000:afq=1.4:amm=sco:anc=all_dependent:bs=on:ccuc=small_ones:cond=fast:fde=none:gsp=input_only:nm=64:nwc=1:sac=on:urr=ec_only:updr=off:uhcvi=on_105 on theBenchmark
% 0.21/0.49  % (9590)lrs+1_5:1_afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:fde=none:gs=on:gsaa=full_model:gsem=on:irw=on:lwlo=on:nm=0:nwc=2.5:stl=30:sp=occurrence:uhcvi=on_42 on theBenchmark
% 0.21/0.50  % (9593)ott-3_4:1_awrs=converge:awrsf=2:acc=model:add=large:afr=on:afp=40000:afq=1.2:anc=none:ccuc=small_ones:fde=unused:gsp=input_only:irw=on:nm=0:nwc=4:sd=4:ss=axioms:s2a=on:st=1.2:sos=on:urr=on:updr=off:uhcvi=on_2 on theBenchmark
% 0.21/0.50  % (9583)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_92 on theBenchmark
% 0.21/0.50  % (9582)Refutation found. Thanks to Tanya!
% 0.21/0.50  % SZS status Theorem for theBenchmark
% 0.21/0.50  % (9585)lrs+1_4:1_awrs=converge:awrsf=128:av=off:cond=fast:fde=none:gsp=input_only:gs=on:gsem=on:lcm=predicate:lwlo=on:nm=4:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:s2a=on:st=2.0:sos=on_27 on theBenchmark
% 0.21/0.50  % SZS output start Proof for theBenchmark
% 0.21/0.50  fof(f530,plain,(
% 0.21/0.50    $false),
% 0.21/0.50    inference(avatar_sat_refutation,[],[f86,f91,f96,f101,f106,f111,f116,f124,f129,f134,f146,f151,f166,f174,f179,f187,f205,f217,f236,f241,f247,f259,f264,f269,f291,f292,f306,f316,f333,f338,f352,f359,f385,f395,f399,f403,f415,f441,f450,f481,f506,f518,f529])).
% 0.21/0.50  fof(f529,plain,(
% 0.21/0.50    ~spl3_41 | ~spl3_45 | ~spl3_49 | spl3_52 | ~spl3_54 | ~spl3_59),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f528])).
% 0.21/0.50  fof(f528,plain,(
% 0.21/0.50    $false | (~spl3_41 | ~spl3_45 | ~spl3_49 | spl3_52 | ~spl3_54 | ~spl3_59)),
% 0.21/0.50    inference(subsumption_resolution,[],[f522,f358])).
% 0.21/0.50  fof(f358,plain,(
% 0.21/0.50    r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | ~spl3_41),
% 0.21/0.50    inference(avatar_component_clause,[],[f356])).
% 0.21/0.50  fof(f356,plain,(
% 0.21/0.50    spl3_41 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_41])])).
% 0.21/0.50  fof(f522,plain,(
% 0.21/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | (~spl3_45 | ~spl3_49 | spl3_52 | ~spl3_54 | ~spl3_59)),
% 0.21/0.50    inference(backward_demodulation,[],[f440,f521])).
% 0.21/0.50  fof(f521,plain,(
% 0.21/0.50    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_45 | ~spl3_49 | ~spl3_54 | ~spl3_59)),
% 0.21/0.50    inference(subsumption_resolution,[],[f520,f394])).
% 0.21/0.50  fof(f394,plain,(
% 0.21/0.50    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~spl3_45),
% 0.21/0.50    inference(avatar_component_clause,[],[f392])).
% 0.21/0.50  fof(f392,plain,(
% 0.21/0.50    spl3_45 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_45])])).
% 0.21/0.50  fof(f520,plain,(
% 0.21/0.50    sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | (~spl3_49 | ~spl3_54 | ~spl3_59)),
% 0.21/0.50    inference(subsumption_resolution,[],[f519,f480])).
% 0.21/0.50  fof(f480,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_54),
% 0.21/0.50    inference(avatar_component_clause,[],[f478])).
% 0.21/0.50  fof(f478,plain,(
% 0.21/0.50    spl3_54 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_54])])).
% 0.21/0.50  fof(f519,plain,(
% 0.21/0.50    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | sK2 = k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | (~spl3_49 | ~spl3_59)),
% 0.21/0.50    inference(resolution,[],[f517,f414])).
% 0.21/0.50  fof(f414,plain,(
% 0.21/0.50    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_49),
% 0.21/0.50    inference(avatar_component_clause,[],[f412])).
% 0.21/0.50  fof(f412,plain,(
% 0.21/0.50    spl3_49 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_49])])).
% 0.21/0.50  fof(f517,plain,(
% 0.21/0.50    ( ! [X6,X7] : (~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | k2_relset_1(X6,X7,k2_funct_1(sK2)) != X7 | sK2 = k2_tops_2(X6,X7,k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),X6,X7)) ) | ~spl3_59),
% 0.21/0.50    inference(avatar_component_clause,[],[f516])).
% 0.21/0.50  fof(f516,plain,(
% 0.21/0.50    spl3_59 <=> ! [X7,X6] : (sK2 = k2_tops_2(X6,X7,k2_funct_1(sK2)) | k2_relset_1(X6,X7,k2_funct_1(sK2)) != X7 | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_2(k2_funct_1(sK2),X6,X7))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_59])])).
% 0.21/0.50  fof(f440,plain,(
% 0.21/0.50    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) | spl3_52),
% 0.21/0.50    inference(avatar_component_clause,[],[f438])).
% 0.21/0.50  fof(f438,plain,(
% 0.21/0.50    spl3_52 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_52])])).
% 0.21/0.50  fof(f518,plain,(
% 0.21/0.50    spl3_59 | ~spl3_18 | ~spl3_42 | ~spl3_56),
% 0.21/0.50    inference(avatar_split_clause,[],[f514,f493,f361,f184,f516])).
% 0.21/0.50  fof(f184,plain,(
% 0.21/0.50    spl3_18 <=> sK2 = k2_funct_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.50  fof(f361,plain,(
% 0.21/0.50    spl3_42 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_42])])).
% 0.21/0.50  fof(f493,plain,(
% 0.21/0.50    spl3_56 <=> v2_funct_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_56])])).
% 0.21/0.50  fof(f514,plain,(
% 0.21/0.50    ( ! [X6,X7] : (sK2 = k2_tops_2(X6,X7,k2_funct_1(sK2)) | k2_relset_1(X6,X7,k2_funct_1(sK2)) != X7 | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_2(k2_funct_1(sK2),X6,X7)) ) | (~spl3_18 | ~spl3_42 | ~spl3_56)),
% 0.21/0.50    inference(subsumption_resolution,[],[f467,f494])).
% 0.21/0.50  fof(f494,plain,(
% 0.21/0.50    v2_funct_1(k2_funct_1(sK2)) | ~spl3_56),
% 0.21/0.50    inference(avatar_component_clause,[],[f493])).
% 0.21/0.50  fof(f467,plain,(
% 0.21/0.50    ( ! [X6,X7] : (sK2 = k2_tops_2(X6,X7,k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | k2_relset_1(X6,X7,k2_funct_1(sK2)) != X7 | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_2(k2_funct_1(sK2),X6,X7)) ) | (~spl3_18 | ~spl3_42)),
% 0.21/0.50    inference(forward_demodulation,[],[f457,f186])).
% 0.21/0.50  fof(f186,plain,(
% 0.21/0.50    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl3_18),
% 0.21/0.50    inference(avatar_component_clause,[],[f184])).
% 0.21/0.50  fof(f457,plain,(
% 0.21/0.50    ( ! [X6,X7] : (~v2_funct_1(k2_funct_1(sK2)) | k2_relset_1(X6,X7,k2_funct_1(sK2)) != X7 | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X6,X7))) | ~v1_funct_2(k2_funct_1(sK2),X6,X7) | k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X6,X7,k2_funct_1(sK2))) ) | ~spl3_42),
% 0.21/0.50    inference(resolution,[],[f363,f72])).
% 0.21/0.50  fof(f72,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f35])).
% 0.21/0.50  fof(f35,plain,(
% 0.21/0.50    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.50    inference(flattening,[],[f34])).
% 0.21/0.50  fof(f34,plain,(
% 0.21/0.50    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.50    inference(ennf_transformation,[],[f13])).
% 0.21/0.50  fof(f13,axiom,(
% 0.21/0.50    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 0.21/0.50  fof(f363,plain,(
% 0.21/0.50    v1_funct_1(k2_funct_1(sK2)) | ~spl3_42),
% 0.21/0.50    inference(avatar_component_clause,[],[f361])).
% 0.21/0.50  fof(f506,plain,(
% 0.21/0.50    ~spl3_4 | ~spl3_5 | ~spl3_16 | spl3_56),
% 0.21/0.50    inference(avatar_contradiction_clause,[],[f505])).
% 0.21/0.50  fof(f505,plain,(
% 0.21/0.50    $false | (~spl3_4 | ~spl3_5 | ~spl3_16 | spl3_56)),
% 0.21/0.50    inference(subsumption_resolution,[],[f504,f173])).
% 0.21/0.50  fof(f173,plain,(
% 0.21/0.50    v1_relat_1(sK2) | ~spl3_16),
% 0.21/0.50    inference(avatar_component_clause,[],[f171])).
% 0.21/0.50  fof(f171,plain,(
% 0.21/0.50    spl3_16 <=> v1_relat_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.50  fof(f504,plain,(
% 0.21/0.50    ~v1_relat_1(sK2) | (~spl3_4 | ~spl3_5 | spl3_56)),
% 0.21/0.50    inference(subsumption_resolution,[],[f503,f100])).
% 0.21/0.50  fof(f100,plain,(
% 0.21/0.50    v1_funct_1(sK2) | ~spl3_4),
% 0.21/0.50    inference(avatar_component_clause,[],[f98])).
% 0.21/0.50  fof(f98,plain,(
% 0.21/0.50    spl3_4 <=> v1_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.50  fof(f503,plain,(
% 0.21/0.50    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | (~spl3_5 | spl3_56)),
% 0.21/0.50    inference(subsumption_resolution,[],[f501,f105])).
% 0.21/0.50  fof(f105,plain,(
% 0.21/0.50    v2_funct_1(sK2) | ~spl3_5),
% 0.21/0.50    inference(avatar_component_clause,[],[f103])).
% 0.21/0.50  fof(f103,plain,(
% 0.21/0.50    spl3_5 <=> v2_funct_1(sK2)),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.50  fof(f501,plain,(
% 0.21/0.50    ~v2_funct_1(sK2) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_56),
% 0.21/0.50    inference(resolution,[],[f495,f56])).
% 0.21/0.50  fof(f56,plain,(
% 0.21/0.50    ( ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f22])).
% 0.21/0.50  fof(f22,plain,(
% 0.21/0.50    ! [X0] : (v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.50    inference(flattening,[],[f21])).
% 0.21/0.50  fof(f21,plain,(
% 0.21/0.50    ! [X0] : ((v2_funct_1(k2_funct_1(X0)) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.50    inference(ennf_transformation,[],[f3])).
% 0.21/0.50  fof(f3,axiom,(
% 0.21/0.50    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => v2_funct_1(k2_funct_1(X0))))),
% 0.21/0.50    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t62_funct_1)).
% 0.21/0.50  fof(f495,plain,(
% 0.21/0.50    ~v2_funct_1(k2_funct_1(sK2)) | spl3_56),
% 0.21/0.50    inference(avatar_component_clause,[],[f493])).
% 0.21/0.50  fof(f481,plain,(
% 0.21/0.50    spl3_54 | ~spl3_20 | ~spl3_49),
% 0.21/0.50    inference(avatar_split_clause,[],[f424,f412,f202,f478])).
% 0.21/0.50  fof(f202,plain,(
% 0.21/0.50    spl3_20 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 0.21/0.50    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.50  fof(f424,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (~spl3_20 | ~spl3_49)),
% 0.21/0.50    inference(forward_demodulation,[],[f420,f204])).
% 0.21/0.50  fof(f204,plain,(
% 0.21/0.50    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_20),
% 0.21/0.50    inference(avatar_component_clause,[],[f202])).
% 0.21/0.50  fof(f420,plain,(
% 0.21/0.50    k2_relat_1(k2_funct_1(sK2)) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | ~spl3_49),
% 0.21/0.50    inference(resolution,[],[f414,f62])).
% 0.21/0.50  fof(f62,plain,(
% 0.21/0.50    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.50    inference(cnf_transformation,[],[f29])).
% 0.21/0.51  fof(f29,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f7])).
% 0.21/0.51  fof(f7,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.51  fof(f450,plain,(
% 0.21/0.51    ~spl3_4 | ~spl3_5 | ~spl3_33 | ~spl3_35 | ~spl3_38 | spl3_42),
% 0.21/0.51    inference(avatar_contradiction_clause,[],[f449])).
% 0.21/0.51  fof(f449,plain,(
% 0.21/0.51    $false | (~spl3_4 | ~spl3_5 | ~spl3_33 | ~spl3_35 | ~spl3_38 | spl3_42)),
% 0.21/0.51    inference(unit_resulting_resolution,[],[f100,f105,f305,f315,f337,f362,f69])).
% 0.21/0.51  fof(f69,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | v1_funct_1(k2_funct_1(X2))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f33,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f32])).
% 0.21/0.51  fof(f32,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f10])).
% 0.21/0.51  fof(f10,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.51  fof(f362,plain,(
% 0.21/0.51    ~v1_funct_1(k2_funct_1(sK2)) | spl3_42),
% 0.21/0.51    inference(avatar_component_clause,[],[f361])).
% 0.21/0.51  fof(f337,plain,(
% 0.21/0.51    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~spl3_38),
% 0.21/0.51    inference(avatar_component_clause,[],[f335])).
% 0.21/0.51  fof(f335,plain,(
% 0.21/0.51    spl3_38 <=> k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_38])])).
% 0.21/0.51  fof(f315,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~spl3_35),
% 0.21/0.51    inference(avatar_component_clause,[],[f313])).
% 0.21/0.51  fof(f313,plain,(
% 0.21/0.51    spl3_35 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.21/0.51  fof(f305,plain,(
% 0.21/0.51    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~spl3_33),
% 0.21/0.51    inference(avatar_component_clause,[],[f303])).
% 0.21/0.51  fof(f303,plain,(
% 0.21/0.51    spl3_33 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.51  fof(f441,plain,(
% 0.21/0.51    ~spl3_52 | ~spl3_33 | ~spl3_35 | spl3_37 | ~spl3_38 | ~spl3_47),
% 0.21/0.51    inference(avatar_split_clause,[],[f426,f401,f335,f330,f313,f303,f438])).
% 0.21/0.51  fof(f330,plain,(
% 0.21/0.51    spl3_37 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_37])])).
% 0.21/0.51  fof(f401,plain,(
% 0.21/0.51    spl3_47 <=> ! [X1,X0] : (k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.21/0.51  fof(f426,plain,(
% 0.21/0.51    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) | (~spl3_33 | ~spl3_35 | spl3_37 | ~spl3_38 | ~spl3_47)),
% 0.21/0.51    inference(backward_demodulation,[],[f332,f418])).
% 0.21/0.51  fof(f418,plain,(
% 0.21/0.51    k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_33 | ~spl3_35 | ~spl3_38 | ~spl3_47)),
% 0.21/0.51    inference(subsumption_resolution,[],[f417,f305])).
% 0.21/0.51  fof(f417,plain,(
% 0.21/0.51    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_35 | ~spl3_38 | ~spl3_47)),
% 0.21/0.51    inference(subsumption_resolution,[],[f416,f337])).
% 0.21/0.51  fof(f416,plain,(
% 0.21/0.51    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k2_funct_1(sK2) = k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_35 | ~spl3_47)),
% 0.21/0.51    inference(resolution,[],[f402,f315])).
% 0.21/0.51  fof(f402,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_2(sK2,X0,X1) | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)) ) | ~spl3_47),
% 0.21/0.51    inference(avatar_component_clause,[],[f401])).
% 0.21/0.51  fof(f332,plain,(
% 0.21/0.51    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) | spl3_37),
% 0.21/0.51    inference(avatar_component_clause,[],[f330])).
% 0.21/0.51  fof(f415,plain,(
% 0.21/0.51    spl3_49 | ~spl3_33 | ~spl3_35 | ~spl3_38 | ~spl3_46),
% 0.21/0.51    inference(avatar_split_clause,[],[f410,f397,f335,f313,f303,f412])).
% 0.21/0.51  fof(f397,plain,(
% 0.21/0.51    spl3_46 <=> ! [X1,X0] : (k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.21/0.51  fof(f410,plain,(
% 0.21/0.51    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_33 | ~spl3_35 | ~spl3_38 | ~spl3_46)),
% 0.21/0.51    inference(subsumption_resolution,[],[f409,f305])).
% 0.21/0.51  fof(f409,plain,(
% 0.21/0.51    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_35 | ~spl3_38 | ~spl3_46)),
% 0.21/0.51    inference(subsumption_resolution,[],[f408,f337])).
% 0.21/0.51  fof(f408,plain,(
% 0.21/0.51    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_35 | ~spl3_46)),
% 0.21/0.51    inference(resolution,[],[f398,f315])).
% 0.21/0.51  fof(f398,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_2(sK2,X0,X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | ~spl3_46),
% 0.21/0.51    inference(avatar_component_clause,[],[f397])).
% 0.21/0.51  fof(f403,plain,(
% 0.21/0.51    spl3_47 | ~spl3_4 | ~spl3_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f294,f103,f98,f401])).
% 0.21/0.51  fof(f294,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)) ) | (~spl3_4 | ~spl3_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f293,f105])).
% 0.21/0.51  fof(f293,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~v2_funct_1(sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)) ) | ~spl3_4),
% 0.21/0.51    inference(resolution,[],[f72,f100])).
% 0.21/0.51  fof(f399,plain,(
% 0.21/0.51    spl3_46 | ~spl3_4 | ~spl3_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f282,f103,f98,f397])).
% 0.21/0.51  fof(f282,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | (~spl3_4 | ~spl3_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f281,f105])).
% 0.21/0.51  fof(f281,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) ) | ~spl3_4),
% 0.21/0.51    inference(resolution,[],[f71,f100])).
% 0.21/0.51  fof(f71,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f395,plain,(
% 0.21/0.51    spl3_45 | ~spl3_33 | ~spl3_35 | ~spl3_38 | ~spl3_44),
% 0.21/0.51    inference(avatar_split_clause,[],[f390,f383,f335,f313,f303,f392])).
% 0.21/0.51  fof(f383,plain,(
% 0.21/0.51    spl3_44 <=> ! [X1,X0] : (k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | v1_funct_2(k2_funct_1(sK2),X1,X0))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_44])])).
% 0.21/0.51  fof(f390,plain,(
% 0.21/0.51    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | (~spl3_33 | ~spl3_35 | ~spl3_38 | ~spl3_44)),
% 0.21/0.51    inference(subsumption_resolution,[],[f389,f305])).
% 0.21/0.51  fof(f389,plain,(
% 0.21/0.51    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | (~spl3_35 | ~spl3_38 | ~spl3_44)),
% 0.21/0.51    inference(subsumption_resolution,[],[f388,f337])).
% 0.21/0.51  fof(f388,plain,(
% 0.21/0.51    k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | (~spl3_35 | ~spl3_44)),
% 0.21/0.51    inference(resolution,[],[f384,f315])).
% 0.21/0.51  fof(f384,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1 | ~v1_funct_2(sK2,X0,X1) | v1_funct_2(k2_funct_1(sK2),X1,X0)) ) | ~spl3_44),
% 0.21/0.51    inference(avatar_component_clause,[],[f383])).
% 0.21/0.51  fof(f385,plain,(
% 0.21/0.51    spl3_44 | ~spl3_4 | ~spl3_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f279,f103,f98,f383])).
% 0.21/0.51  fof(f279,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | v1_funct_2(k2_funct_1(sK2),X1,X0)) ) | (~spl3_4 | ~spl3_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f278,f105])).
% 0.21/0.51  fof(f278,plain,(
% 0.21/0.51    ( ! [X0,X1] : (k2_relset_1(X0,X1,sK2) != X1 | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | v1_funct_2(k2_funct_1(sK2),X1,X0)) ) | ~spl3_4),
% 0.21/0.51    inference(resolution,[],[f70,f100])).
% 0.21/0.51  fof(f70,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~v1_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | v1_funct_2(k2_funct_1(X2),X1,X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f33])).
% 0.21/0.51  fof(f359,plain,(
% 0.21/0.51    spl3_41 | ~spl3_33 | ~spl3_35 | ~spl3_40),
% 0.21/0.51    inference(avatar_split_clause,[],[f354,f350,f313,f303,f356])).
% 0.21/0.51  fof(f350,plain,(
% 0.21/0.51    spl3_40 <=> ! [X1,X0] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | r2_funct_2(X0,X1,sK2,sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_40])])).
% 0.21/0.51  fof(f354,plain,(
% 0.21/0.51    r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | (~spl3_33 | ~spl3_35 | ~spl3_40)),
% 0.21/0.51    inference(subsumption_resolution,[],[f353,f305])).
% 0.21/0.51  fof(f353,plain,(
% 0.21/0.51    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | (~spl3_35 | ~spl3_40)),
% 0.21/0.51    inference(resolution,[],[f351,f315])).
% 0.21/0.51  fof(f351,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | r2_funct_2(X0,X1,sK2,sK2)) ) | ~spl3_40),
% 0.21/0.51    inference(avatar_component_clause,[],[f350])).
% 0.21/0.51  fof(f352,plain,(
% 0.21/0.51    spl3_40 | ~spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f270,f98,f350])).
% 0.21/0.51  fof(f270,plain,(
% 0.21/0.51    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | r2_funct_2(X0,X1,sK2,sK2)) ) | ~spl3_4),
% 0.21/0.51    inference(resolution,[],[f81,f100])).
% 0.21/0.51  fof(f81,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | r2_funct_2(X0,X1,X3,X3)) )),
% 0.21/0.51    inference(duplicate_literal_removal,[],[f80])).
% 0.21/0.51  fof(f80,plain,(
% 0.21/0.51    ( ! [X0,X3,X1] : (r2_funct_2(X0,X1,X3,X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3)) )),
% 0.21/0.51    inference(equality_resolution,[],[f74])).
% 0.21/0.51  fof(f74,plain,(
% 0.21/0.51    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X3) | X2 != X3 | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f43])).
% 0.21/0.51  fof(f43,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : (((r2_funct_2(X0,X1,X2,X3) | X2 != X3) & (X2 = X3 | ~r2_funct_2(X0,X1,X2,X3))) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(nnf_transformation,[],[f37])).
% 0.21/0.51  fof(f37,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.51    inference(flattening,[],[f36])).
% 0.21/0.51  fof(f36,plain,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((r2_funct_2(X0,X1,X2,X3) <=> X2 = X3) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.51    inference(ennf_transformation,[],[f9])).
% 0.21/0.51  fof(f9,axiom,(
% 0.21/0.51    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (r2_funct_2(X0,X1,X2,X3) <=> X2 = X3))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_r2_funct_2)).
% 0.21/0.51  fof(f338,plain,(
% 0.21/0.51    spl3_38 | ~spl3_29 | ~spl3_32),
% 0.21/0.51    inference(avatar_split_clause,[],[f300,f288,f261,f335])).
% 0.21/0.51  fof(f261,plain,(
% 0.21/0.51    spl3_29 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.51  fof(f288,plain,(
% 0.21/0.51    spl3_32 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_32])])).
% 0.21/0.51  fof(f300,plain,(
% 0.21/0.51    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_29 | ~spl3_32)),
% 0.21/0.51    inference(backward_demodulation,[],[f263,f290])).
% 0.21/0.51  fof(f290,plain,(
% 0.21/0.51    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_32),
% 0.21/0.51    inference(avatar_component_clause,[],[f288])).
% 0.21/0.51  fof(f263,plain,(
% 0.21/0.51    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_29),
% 0.21/0.51    inference(avatar_component_clause,[],[f261])).
% 0.21/0.51  fof(f333,plain,(
% 0.21/0.51    ~spl3_37 | spl3_28 | ~spl3_32),
% 0.21/0.51    inference(avatar_split_clause,[],[f299,f288,f256,f330])).
% 0.21/0.51  fof(f256,plain,(
% 0.21/0.51    spl3_28 <=> r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 0.21/0.51  fof(f299,plain,(
% 0.21/0.51    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) | (spl3_28 | ~spl3_32)),
% 0.21/0.51    inference(backward_demodulation,[],[f258,f290])).
% 0.21/0.51  fof(f258,plain,(
% 0.21/0.51    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) | spl3_28),
% 0.21/0.51    inference(avatar_component_clause,[],[f256])).
% 0.21/0.51  fof(f316,plain,(
% 0.21/0.51    spl3_35 | ~spl3_27 | ~spl3_32),
% 0.21/0.51    inference(avatar_split_clause,[],[f298,f288,f244,f313])).
% 0.21/0.51  fof(f244,plain,(
% 0.21/0.51    spl3_27 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.51  fof(f298,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_27 | ~spl3_32)),
% 0.21/0.51    inference(backward_demodulation,[],[f246,f290])).
% 0.21/0.51  fof(f246,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_27),
% 0.21/0.51    inference(avatar_component_clause,[],[f244])).
% 0.21/0.51  fof(f306,plain,(
% 0.21/0.51    spl3_33 | ~spl3_25 | ~spl3_32),
% 0.21/0.51    inference(avatar_split_clause,[],[f297,f288,f233,f303])).
% 0.21/0.51  fof(f233,plain,(
% 0.21/0.51    spl3_25 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 0.21/0.51  fof(f297,plain,(
% 0.21/0.51    v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | (~spl3_25 | ~spl3_32)),
% 0.21/0.51    inference(backward_demodulation,[],[f235,f290])).
% 0.21/0.51  fof(f235,plain,(
% 0.21/0.51    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_25),
% 0.21/0.51    inference(avatar_component_clause,[],[f233])).
% 0.21/0.51  fof(f292,plain,(
% 0.21/0.51    k1_xboole_0 != k2_relat_1(sK2) | k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) != k2_relat_1(sK2) | k2_struct_0(sK1) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | v1_xboole_0(k2_struct_0(sK1)) | ~v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.51  fof(f291,plain,(
% 0.21/0.51    spl3_31 | spl3_32 | ~spl3_25 | ~spl3_27 | ~spl3_30),
% 0.21/0.51    inference(avatar_split_clause,[],[f280,f266,f244,f233,f288,f284])).
% 0.21/0.51  fof(f284,plain,(
% 0.21/0.51    spl3_31 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_31])])).
% 0.21/0.51  fof(f266,plain,(
% 0.21/0.51    spl3_30 <=> k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.51  fof(f280,plain,(
% 0.21/0.51    k2_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2) | (~spl3_25 | ~spl3_27 | ~spl3_30)),
% 0.21/0.51    inference(forward_demodulation,[],[f273,f268])).
% 0.21/0.51  fof(f268,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_30),
% 0.21/0.51    inference(avatar_component_clause,[],[f266])).
% 0.21/0.51  fof(f273,plain,(
% 0.21/0.51    k1_xboole_0 = k2_relat_1(sK2) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | (~spl3_25 | ~spl3_27)),
% 0.21/0.51    inference(subsumption_resolution,[],[f272,f235])).
% 0.21/0.51  fof(f272,plain,(
% 0.21/0.51    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2) | k2_struct_0(sK0) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_27),
% 0.21/0.51    inference(resolution,[],[f63,f246])).
% 0.21/0.51  fof(f63,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | k1_xboole_0 = X1 | k1_relset_1(X0,X1,X2) = X0) )),
% 0.21/0.51    inference(cnf_transformation,[],[f42])).
% 0.21/0.51  fof(f42,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) | k1_xboole_0 != X2) & (k1_xboole_0 = X2 | ~v1_funct_2(X2,X0,X1))) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & (((v1_funct_2(X2,X0,X1) | k1_relset_1(X0,X1,X2) != X0) & (k1_relset_1(X0,X1,X2) = X0 | ~v1_funct_2(X2,X0,X1))) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(nnf_transformation,[],[f31])).
% 0.21/0.51  fof(f31,plain,(
% 0.21/0.51    ! [X0,X1,X2] : ((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0 | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(flattening,[],[f30])).
% 0.21/0.51  fof(f30,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (((((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0) | k1_xboole_0 != X1) & ((v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f8])).
% 0.21/0.51  fof(f8,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => ((k1_xboole_0 = X1 => ((v1_funct_2(X2,X0,X1) <=> k1_xboole_0 = X2) | k1_xboole_0 = X0)) & ((k1_xboole_0 = X1 => k1_xboole_0 = X0) => (v1_funct_2(X2,X0,X1) <=> k1_relset_1(X0,X1,X2) = X0))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_funct_2)).
% 0.21/0.51  fof(f269,plain,(
% 0.21/0.51    spl3_30 | ~spl3_27),
% 0.21/0.51    inference(avatar_split_clause,[],[f249,f244,f266])).
% 0.21/0.51  fof(f249,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_27),
% 0.21/0.51    inference(resolution,[],[f246,f61])).
% 0.21/0.51  fof(f61,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f28])).
% 0.21/0.51  fof(f28,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f6])).
% 0.21/0.51  fof(f6,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.51  fof(f264,plain,(
% 0.21/0.51    spl3_29 | ~spl3_27),
% 0.21/0.51    inference(avatar_split_clause,[],[f248,f244,f261])).
% 0.21/0.51  fof(f248,plain,(
% 0.21/0.51    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_27),
% 0.21/0.51    inference(resolution,[],[f246,f62])).
% 0.21/0.51  fof(f259,plain,(
% 0.21/0.51    ~spl3_28 | ~spl3_8 | ~spl3_26),
% 0.21/0.51    inference(avatar_split_clause,[],[f253,f238,f121,f256])).
% 0.21/0.51  fof(f121,plain,(
% 0.21/0.51    spl3_8 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.51  fof(f238,plain,(
% 0.21/0.51    spl3_26 <=> u1_struct_0(sK1) = k2_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.51  fof(f253,plain,(
% 0.21/0.51    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) | (~spl3_8 | ~spl3_26)),
% 0.21/0.51    inference(forward_demodulation,[],[f252,f123])).
% 0.21/0.51  fof(f123,plain,(
% 0.21/0.51    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_8),
% 0.21/0.51    inference(avatar_component_clause,[],[f121])).
% 0.21/0.51  fof(f252,plain,(
% 0.21/0.51    ~r2_funct_2(u1_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) | ~spl3_26),
% 0.21/0.51    inference(forward_demodulation,[],[f52,f240])).
% 0.21/0.51  fof(f240,plain,(
% 0.21/0.51    u1_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_26),
% 0.21/0.51    inference(avatar_component_clause,[],[f238])).
% 0.21/0.51  fof(f52,plain,(
% 0.21/0.51    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f41,plain,(
% 0.21/0.51    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.21/0.51    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f17,f40,f39,f38])).
% 0.21/0.51  fof(f38,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f39,plain,(
% 0.21/0.51    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f40,plain,(
% 0.21/0.51    ? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.21/0.51    introduced(choice_axiom,[])).
% 0.21/0.51  fof(f17,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f16])).
% 0.21/0.51  fof(f16,plain,(
% 0.21/0.51    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f15])).
% 0.21/0.51  fof(f15,negated_conjecture,(
% 0.21/0.51    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.21/0.51    inference(negated_conjecture,[],[f14])).
% 0.21/0.51  fof(f14,conjecture,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).
% 0.21/0.51  fof(f247,plain,(
% 0.21/0.51    spl3_27 | ~spl3_15 | ~spl3_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f218,f176,f163,f244])).
% 0.21/0.51  fof(f163,plain,(
% 0.21/0.51    spl3_15 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.51  fof(f176,plain,(
% 0.21/0.51    spl3_17 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 0.21/0.51  fof(f218,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | (~spl3_15 | ~spl3_17)),
% 0.21/0.51    inference(backward_demodulation,[],[f165,f212])).
% 0.21/0.51  fof(f212,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_15 | ~spl3_17)),
% 0.21/0.51    inference(backward_demodulation,[],[f178,f206])).
% 0.21/0.51  fof(f206,plain,(
% 0.21/0.51    k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2) | ~spl3_15),
% 0.21/0.51    inference(resolution,[],[f62,f165])).
% 0.21/0.51  fof(f178,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_17),
% 0.21/0.51    inference(avatar_component_clause,[],[f176])).
% 0.21/0.51  fof(f165,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_15),
% 0.21/0.51    inference(avatar_component_clause,[],[f163])).
% 0.21/0.51  fof(f241,plain,(
% 0.21/0.51    spl3_26 | ~spl3_10 | ~spl3_15 | ~spl3_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f221,f176,f163,f131,f238])).
% 0.21/0.51  fof(f131,plain,(
% 0.21/0.51    spl3_10 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.51  fof(f221,plain,(
% 0.21/0.51    u1_struct_0(sK1) = k2_relat_1(sK2) | (~spl3_10 | ~spl3_15 | ~spl3_17)),
% 0.21/0.51    inference(backward_demodulation,[],[f133,f212])).
% 0.21/0.51  fof(f133,plain,(
% 0.21/0.51    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_10),
% 0.21/0.51    inference(avatar_component_clause,[],[f131])).
% 0.21/0.51  fof(f236,plain,(
% 0.21/0.51    spl3_25 | ~spl3_11 | ~spl3_15 | ~spl3_17),
% 0.21/0.51    inference(avatar_split_clause,[],[f220,f176,f163,f143,f233])).
% 0.21/0.51  fof(f143,plain,(
% 0.21/0.51    spl3_11 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.51  fof(f220,plain,(
% 0.21/0.51    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | (~spl3_11 | ~spl3_15 | ~spl3_17)),
% 0.21/0.51    inference(backward_demodulation,[],[f145,f212])).
% 0.21/0.51  fof(f145,plain,(
% 0.21/0.51    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~spl3_11),
% 0.21/0.51    inference(avatar_component_clause,[],[f143])).
% 0.21/0.51  fof(f217,plain,(
% 0.21/0.51    spl3_22 | ~spl3_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f206,f163,f214])).
% 0.21/0.51  fof(f214,plain,(
% 0.21/0.51    spl3_22 <=> k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) = k2_relat_1(sK2)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.51  fof(f205,plain,(
% 0.21/0.51    spl3_20 | ~spl3_4 | ~spl3_5 | ~spl3_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f194,f171,f103,f98,f202])).
% 0.21/0.51  fof(f194,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f193,f173])).
% 0.21/0.51  fof(f193,plain,(
% 0.21/0.51    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | (~spl3_4 | ~spl3_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f192,f105])).
% 0.21/0.51  fof(f192,plain,(
% 0.21/0.51    ~v2_funct_1(sK2) | k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~spl3_4),
% 0.21/0.51    inference(resolution,[],[f59,f100])).
% 0.21/0.51  fof(f59,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f26])).
% 0.21/0.51  fof(f26,plain,(
% 0.21/0.51    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f25])).
% 0.21/0.51  fof(f25,plain,(
% 0.21/0.51    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f2])).
% 0.21/0.51  fof(f2,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 0.21/0.51  fof(f187,plain,(
% 0.21/0.51    spl3_18 | ~spl3_4 | ~spl3_5 | ~spl3_16),
% 0.21/0.51    inference(avatar_split_clause,[],[f182,f171,f103,f98,f184])).
% 0.21/0.51  fof(f182,plain,(
% 0.21/0.51    sK2 = k2_funct_1(k2_funct_1(sK2)) | (~spl3_4 | ~spl3_5 | ~spl3_16)),
% 0.21/0.51    inference(subsumption_resolution,[],[f181,f173])).
% 0.21/0.51  fof(f181,plain,(
% 0.21/0.51    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | (~spl3_4 | ~spl3_5)),
% 0.21/0.51    inference(subsumption_resolution,[],[f180,f105])).
% 0.21/0.51  % (9591)lrs+1011_2:3_add=large:afr=on:afp=100000:afq=1.2:anc=none:gs=on:gsem=off:irw=on:nm=64:nwc=1:stl=30:sd=3:ss=axioms:sos=all:sp=reverse_arity_48 on theBenchmark
% 0.21/0.51  fof(f180,plain,(
% 0.21/0.51    ~v2_funct_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(sK2) | ~spl3_4),
% 0.21/0.51    inference(resolution,[],[f57,f100])).
% 0.21/0.51  fof(f57,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_funct_1(X0) | ~v2_funct_1(X0) | k2_funct_1(k2_funct_1(X0)) = X0 | ~v1_relat_1(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f24])).
% 0.21/0.51  fof(f24,plain,(
% 0.21/0.51    ! [X0] : (k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.51    inference(flattening,[],[f23])).
% 0.21/0.51  fof(f23,plain,(
% 0.21/0.51    ! [X0] : ((k2_funct_1(k2_funct_1(X0)) = X0 | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f4])).
% 0.21/0.51  fof(f4,axiom,(
% 0.21/0.51    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => k2_funct_1(k2_funct_1(X0)) = X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_funct_1)).
% 0.21/0.51  fof(f179,plain,(
% 0.21/0.51    spl3_17 | ~spl3_8 | ~spl3_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f169,f131,f121,f176])).
% 0.21/0.51  fof(f169,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_8 | ~spl3_10)),
% 0.21/0.51    inference(forward_demodulation,[],[f168,f123])).
% 0.21/0.51  fof(f168,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_10),
% 0.21/0.51    inference(forward_demodulation,[],[f50,f133])).
% 0.21/0.51  fof(f50,plain,(
% 0.21/0.51    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f174,plain,(
% 0.21/0.51    spl3_16 | ~spl3_15),
% 0.21/0.51    inference(avatar_split_clause,[],[f167,f163,f171])).
% 0.21/0.51  fof(f167,plain,(
% 0.21/0.51    v1_relat_1(sK2) | ~spl3_15),
% 0.21/0.51    inference(resolution,[],[f60,f165])).
% 0.21/0.51  fof(f60,plain,(
% 0.21/0.51    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f27])).
% 0.21/0.51  fof(f27,plain,(
% 0.21/0.51    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.51    inference(ennf_transformation,[],[f5])).
% 0.21/0.51  fof(f5,axiom,(
% 0.21/0.51    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.51  fof(f166,plain,(
% 0.21/0.51    spl3_15 | ~spl3_8 | ~spl3_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f152,f131,f121,f163])).
% 0.21/0.51  fof(f152,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_8 | ~spl3_10)),
% 0.21/0.51    inference(forward_demodulation,[],[f137,f133])).
% 0.21/0.51  fof(f137,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_8),
% 0.21/0.51    inference(forward_demodulation,[],[f49,f123])).
% 0.21/0.51  fof(f49,plain,(
% 0.21/0.51    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f151,plain,(
% 0.21/0.51    ~spl3_12 | spl3_2 | ~spl3_3 | ~spl3_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f141,f131,f93,f88,f148])).
% 0.21/0.51  fof(f148,plain,(
% 0.21/0.51    spl3_12 <=> v1_xboole_0(k2_struct_0(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.51  fof(f88,plain,(
% 0.21/0.51    spl3_2 <=> v2_struct_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.51  fof(f93,plain,(
% 0.21/0.51    spl3_3 <=> l1_struct_0(sK1)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.51  fof(f141,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_struct_0(sK1)) | (spl3_2 | ~spl3_3 | ~spl3_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f140,f90])).
% 0.21/0.51  fof(f90,plain,(
% 0.21/0.51    ~v2_struct_0(sK1) | spl3_2),
% 0.21/0.51    inference(avatar_component_clause,[],[f88])).
% 0.21/0.51  fof(f140,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_struct_0(sK1)) | v2_struct_0(sK1) | (~spl3_3 | ~spl3_10)),
% 0.21/0.51    inference(subsumption_resolution,[],[f139,f95])).
% 0.21/0.51  fof(f95,plain,(
% 0.21/0.51    l1_struct_0(sK1) | ~spl3_3),
% 0.21/0.51    inference(avatar_component_clause,[],[f93])).
% 0.21/0.51  fof(f139,plain,(
% 0.21/0.51    ~v1_xboole_0(k2_struct_0(sK1)) | ~l1_struct_0(sK1) | v2_struct_0(sK1) | ~spl3_10),
% 0.21/0.51    inference(superposition,[],[f55,f133])).
% 0.21/0.51  fof(f55,plain,(
% 0.21/0.51    ( ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f20])).
% 0.21/0.51  fof(f20,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 0.21/0.51    inference(flattening,[],[f19])).
% 0.21/0.51  fof(f19,plain,(
% 0.21/0.51    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 0.21/0.51    inference(ennf_transformation,[],[f12])).
% 0.21/0.51  fof(f12,axiom,(
% 0.21/0.51    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 0.21/0.51  fof(f146,plain,(
% 0.21/0.51    spl3_11 | ~spl3_9 | ~spl3_10),
% 0.21/0.51    inference(avatar_split_clause,[],[f138,f131,f126,f143])).
% 0.21/0.51  fof(f126,plain,(
% 0.21/0.51    spl3_9 <=> v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.51  fof(f138,plain,(
% 0.21/0.51    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_9 | ~spl3_10)),
% 0.21/0.51    inference(backward_demodulation,[],[f128,f133])).
% 0.21/0.51  fof(f128,plain,(
% 0.21/0.51    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_9),
% 0.21/0.51    inference(avatar_component_clause,[],[f126])).
% 0.21/0.51  fof(f134,plain,(
% 0.21/0.51    spl3_10 | ~spl3_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f118,f93,f131])).
% 0.21/0.51  fof(f118,plain,(
% 0.21/0.51    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_3),
% 0.21/0.51    inference(resolution,[],[f54,f95])).
% 0.21/0.51  fof(f54,plain,(
% 0.21/0.51    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.51    inference(cnf_transformation,[],[f18])).
% 0.21/0.51  fof(f18,plain,(
% 0.21/0.51    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.51    inference(ennf_transformation,[],[f11])).
% 0.21/0.51  fof(f11,axiom,(
% 0.21/0.51    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.51  fof(f129,plain,(
% 0.21/0.51    spl3_9 | ~spl3_1 | ~spl3_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f119,f113,f83,f126])).
% 0.21/0.51  fof(f83,plain,(
% 0.21/0.51    spl3_1 <=> l1_struct_0(sK0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.51  fof(f113,plain,(
% 0.21/0.51    spl3_7 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.51  fof(f119,plain,(
% 0.21/0.51    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) | (~spl3_1 | ~spl3_7)),
% 0.21/0.51    inference(backward_demodulation,[],[f115,f117])).
% 0.21/0.51  fof(f117,plain,(
% 0.21/0.51    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_1),
% 0.21/0.51    inference(resolution,[],[f54,f85])).
% 0.21/0.51  fof(f85,plain,(
% 0.21/0.51    l1_struct_0(sK0) | ~spl3_1),
% 0.21/0.51    inference(avatar_component_clause,[],[f83])).
% 0.21/0.51  fof(f115,plain,(
% 0.21/0.51    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_7),
% 0.21/0.51    inference(avatar_component_clause,[],[f113])).
% 0.21/0.51  fof(f124,plain,(
% 0.21/0.51    spl3_8 | ~spl3_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f117,f83,f121])).
% 0.21/0.51  fof(f116,plain,(
% 0.21/0.51    spl3_7),
% 0.21/0.51    inference(avatar_split_clause,[],[f48,f113])).
% 0.21/0.51  fof(f48,plain,(
% 0.21/0.51    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f111,plain,(
% 0.21/0.51    spl3_6),
% 0.21/0.51    inference(avatar_split_clause,[],[f53,f108])).
% 0.21/0.51  fof(f108,plain,(
% 0.21/0.51    spl3_6 <=> v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.51  fof(f53,plain,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    inference(cnf_transformation,[],[f1])).
% 0.21/0.51  fof(f1,axiom,(
% 0.21/0.51    v1_xboole_0(k1_xboole_0)),
% 0.21/0.51    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 0.21/0.51  fof(f106,plain,(
% 0.21/0.51    spl3_5),
% 0.21/0.51    inference(avatar_split_clause,[],[f51,f103])).
% 0.21/0.51  fof(f51,plain,(
% 0.21/0.51    v2_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f101,plain,(
% 0.21/0.51    spl3_4),
% 0.21/0.51    inference(avatar_split_clause,[],[f47,f98])).
% 0.21/0.51  fof(f47,plain,(
% 0.21/0.51    v1_funct_1(sK2)),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f96,plain,(
% 0.21/0.51    spl3_3),
% 0.21/0.51    inference(avatar_split_clause,[],[f46,f93])).
% 0.21/0.51  fof(f46,plain,(
% 0.21/0.51    l1_struct_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f91,plain,(
% 0.21/0.51    ~spl3_2),
% 0.21/0.51    inference(avatar_split_clause,[],[f45,f88])).
% 0.21/0.51  fof(f45,plain,(
% 0.21/0.51    ~v2_struct_0(sK1)),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  fof(f86,plain,(
% 0.21/0.51    spl3_1),
% 0.21/0.51    inference(avatar_split_clause,[],[f44,f83])).
% 0.21/0.51  fof(f44,plain,(
% 0.21/0.51    l1_struct_0(sK0)),
% 0.21/0.51    inference(cnf_transformation,[],[f41])).
% 0.21/0.51  % SZS output end Proof for theBenchmark
% 0.21/0.51  % (9582)------------------------------
% 0.21/0.51  % (9582)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.51  % (9582)Termination reason: Refutation
% 0.21/0.51  
% 0.21/0.51  % (9582)Memory used [KB]: 6524
% 0.21/0.51  % (9582)Time elapsed: 0.082 s
% 0.21/0.51  % (9582)------------------------------
% 0.21/0.51  % (9582)------------------------------
% 0.21/0.51  % (9579)Success in time 0.152 s
%------------------------------------------------------------------------------
