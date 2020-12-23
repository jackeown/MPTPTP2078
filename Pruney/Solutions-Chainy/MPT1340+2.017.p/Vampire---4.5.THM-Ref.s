%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:19 EST 2020

% Result     : Theorem 1.38s
% Output     : Refutation 1.38s
% Verified   : 
% Statistics : Number of formulae       :  243 ( 886 expanded)
%              Number of leaves         :   50 ( 356 expanded)
%              Depth                    :   15
%              Number of atoms          :  942 (5458 expanded)
%              Number of equality atoms :  174 ( 860 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f568,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f126,f128,f143,f146,f151,f156,f173,f188,f191,f193,f214,f217,f245,f247,f263,f271,f287,f306,f309,f325,f333,f342,f355,f357,f369,f467,f557,f559,f565])).

fof(f565,plain,
    ( ~ spl3_6
    | ~ spl3_9
    | spl3_50 ),
    inference(avatar_contradiction_clause,[],[f563])).

fof(f563,plain,
    ( $false
    | ~ spl3_6
    | ~ spl3_9
    | spl3_50 ),
    inference(resolution,[],[f562,f172])).

fof(f172,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f170])).

fof(f170,plain,
    ( spl3_9
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f562,plain,
    ( ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_6
    | spl3_50 ),
    inference(trivial_inequality_removal,[],[f561])).

fof(f561,plain,
    ( k1_relat_1(sK2) != k1_relat_1(sK2)
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ spl3_6
    | spl3_50 ),
    inference(forward_demodulation,[],[f560,f155])).

fof(f155,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f153])).

fof(f153,plain,
    ( spl3_6
  <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f560,plain,
    ( k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | spl3_50 ),
    inference(superposition,[],[f552,f85])).

fof(f85,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f40])).

fof(f40,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f9])).

fof(f9,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f552,plain,
    ( k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | spl3_50 ),
    inference(avatar_component_clause,[],[f550])).

fof(f550,plain,
    ( spl3_50
  <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).

fof(f559,plain,
    ( ~ spl3_4
    | ~ spl3_22
    | ~ spl3_21
    | spl3_51 ),
    inference(avatar_split_clause,[],[f558,f554,f276,f280,f136])).

fof(f136,plain,
    ( spl3_4
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f280,plain,
    ( spl3_22
  <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f276,plain,
    ( spl3_21
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f554,plain,
    ( spl3_51
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).

fof(f558,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | spl3_51 ),
    inference(resolution,[],[f556,f103])).

fof(f103,plain,(
    ! [X2,X0,X1] :
      ( r2_funct_2(X1,X2,X0,X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0) ) ),
    inference(duplicate_literal_removal,[],[f102])).

fof(f102,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | r2_funct_2(X1,X2,X0,X0)
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0) ) ),
    inference(condensation,[],[f96])).

fof(f96,plain,(
    ! [X2,X0,X3,X1] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f51])).

fof(f51,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f50])).

fof(f50,plain,(
    ! [X0,X1,X2,X3] :
      ( r2_funct_2(X0,X1,X2,X2)
      | ~ m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X3,X0,X1)
      | ~ v1_funct_1(X3)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f12])).

fof(f12,axiom,(
    ! [X0,X1,X2,X3] :
      ( ( m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X3,X0,X1)
        & v1_funct_1(X3)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => r2_funct_2(X0,X1,X2,X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).

fof(f556,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | spl3_51 ),
    inference(avatar_component_clause,[],[f554])).

fof(f557,plain,
    ( ~ spl3_50
    | ~ spl3_9
    | ~ spl3_12
    | ~ spl3_51
    | spl3_23
    | ~ spl3_28
    | ~ spl3_43 ),
    inference(avatar_split_clause,[],[f548,f464,f367,f284,f554,f185,f170,f550])).

fof(f185,plain,
    ( spl3_12
  <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f284,plain,
    ( spl3_23
  <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).

fof(f367,plain,
    ( spl3_28
  <=> ! [X3,X2] :
        ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X2,X3,k2_funct_1(sK2))
        | ~ v1_funct_2(k2_funct_1(sK2),X2,X3)
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k2_relset_1(X2,X3,k2_funct_1(sK2)) != X3 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).

fof(f464,plain,
    ( spl3_43
  <=> sK2 = k2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).

fof(f548,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)
    | ~ v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))
    | spl3_23
    | ~ spl3_28
    | ~ spl3_43 ),
    inference(superposition,[],[f286,f470])).

fof(f470,plain,
    ( ! [X2,X3] :
        ( sK2 = k2_tops_2(X2,X3,k2_funct_1(sK2))
        | ~ v1_funct_2(k2_funct_1(sK2),X2,X3)
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k2_relset_1(X2,X3,k2_funct_1(sK2)) != X3 )
    | ~ spl3_28
    | ~ spl3_43 ),
    inference(backward_demodulation,[],[f368,f466])).

fof(f466,plain,
    ( sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_43 ),
    inference(avatar_component_clause,[],[f464])).

fof(f368,plain,
    ( ! [X2,X3] :
        ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X2,X3,k2_funct_1(sK2))
        | ~ v1_funct_2(k2_funct_1(sK2),X2,X3)
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | k2_relset_1(X2,X3,k2_funct_1(sK2)) != X3 )
    | ~ spl3_28 ),
    inference(avatar_component_clause,[],[f367])).

fof(f286,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)
    | spl3_23 ),
    inference(avatar_component_clause,[],[f284])).

fof(f467,plain,
    ( spl3_43
    | ~ spl3_4
    | ~ spl3_3
    | ~ spl3_19
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f462,f339,f261,f132,f136,f464])).

fof(f132,plain,
    ( spl3_3
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f261,plain,
    ( spl3_19
  <=> ! [X0] :
        ( k2_relat_1(X0) != k2_relat_1(sK2)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k2_funct_1(k2_funct_1(sK2)) = X0
        | k5_relat_1(X0,k2_funct_1(sK2)) != k6_partfun1(k1_relat_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f339,plain,
    ( spl3_25
  <=> k6_partfun1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).

fof(f462,plain,
    ( ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | ~ spl3_19
    | ~ spl3_25 ),
    inference(trivial_inequality_removal,[],[f461])).

fof(f461,plain,
    ( k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(k1_relat_1(sK2))
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(sK2)
    | sK2 = k2_funct_1(k2_funct_1(sK2))
    | k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ spl3_19
    | ~ spl3_25 ),
    inference(superposition,[],[f262,f341])).

fof(f341,plain,
    ( k6_partfun1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl3_25 ),
    inference(avatar_component_clause,[],[f339])).

fof(f262,plain,
    ( ! [X0] :
        ( k5_relat_1(X0,k2_funct_1(sK2)) != k6_partfun1(k1_relat_1(sK2))
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(X0)
        | k2_funct_1(k2_funct_1(sK2)) = X0
        | k2_relat_1(X0) != k2_relat_1(sK2) )
    | ~ spl3_19 ),
    inference(avatar_component_clause,[],[f261])).

fof(f369,plain,
    ( ~ spl3_8
    | spl3_28
    | ~ spl3_18 ),
    inference(avatar_split_clause,[],[f359,f257,f367,f166])).

fof(f166,plain,
    ( spl3_8
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f257,plain,
    ( spl3_18
  <=> v2_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f359,plain,
    ( ! [X2,X3] :
        ( k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X2,X3,k2_funct_1(sK2))
        | k2_relset_1(X2,X3,k2_funct_1(sK2)) != X3
        | ~ m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        | ~ v1_funct_2(k2_funct_1(sK2),X2,X3)
        | ~ v1_funct_1(k2_funct_1(sK2)) )
    | ~ spl3_18 ),
    inference(resolution,[],[f258,f91])).

fof(f91,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f45])).

fof(f45,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f44])).

fof(f44,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f19])).

fof(f19,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).

fof(f258,plain,
    ( v2_funct_1(k2_funct_1(sK2))
    | ~ spl3_18 ),
    inference(avatar_component_clause,[],[f257])).

fof(f357,plain,(
    spl3_26 ),
    inference(avatar_contradiction_clause,[],[f356])).

fof(f356,plain,
    ( $false
    | spl3_26 ),
    inference(resolution,[],[f354,f97])).

fof(f97,plain,(
    ! [X0] : v2_funct_1(k6_partfun1(X0)) ),
    inference(definition_unfolding,[],[f69,f67])).

fof(f67,plain,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    inference(cnf_transformation,[],[f11])).

fof(f11,axiom,(
    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f69,plain,(
    ! [X0] : v2_funct_1(k6_relat_1(X0)) ),
    inference(cnf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0] :
      ( v2_funct_1(k6_relat_1(X0))
      & v1_relat_1(k6_relat_1(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).

fof(f354,plain,
    ( ~ v2_funct_1(k6_partfun1(k1_relat_1(sK2)))
    | spl3_26 ),
    inference(avatar_component_clause,[],[f352])).

fof(f352,plain,
    ( spl3_26
  <=> v2_funct_1(k6_partfun1(k1_relat_1(sK2))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f355,plain,
    ( ~ spl3_7
    | ~ spl3_8
    | ~ spl3_3
    | ~ spl3_4
    | spl3_18
    | ~ spl3_26
    | ~ spl3_5
    | ~ spl3_25 ),
    inference(avatar_split_clause,[],[f350,f339,f140,f352,f257,f136,f132,f166,f162])).

fof(f162,plain,
    ( spl3_7
  <=> v1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f140,plain,
    ( spl3_5
  <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f350,plain,
    ( ~ v2_funct_1(k6_partfun1(k1_relat_1(sK2)))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_5
    | ~ spl3_25 ),
    inference(trivial_inequality_removal,[],[f349])).

fof(f349,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v2_funct_1(k6_partfun1(k1_relat_1(sK2)))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_5
    | ~ spl3_25 ),
    inference(forward_demodulation,[],[f347,f142])).

fof(f142,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f140])).

fof(f347,plain,
    ( ~ v2_funct_1(k6_partfun1(k1_relat_1(sK2)))
    | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2))
    | v2_funct_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_25 ),
    inference(superposition,[],[f81,f341])).

fof(f81,plain,(
    ! [X0,X1] :
      ( ~ v2_funct_1(k5_relat_1(X1,X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f36])).

fof(f36,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f35])).

fof(f35,plain,(
    ! [X0] :
      ( ! [X1] :
          ( ( v2_funct_1(X0)
            & v2_funct_1(X1) )
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(k5_relat_1(X1,X0))
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(k5_relat_1(X1,X0)) )
           => ( v2_funct_1(X0)
              & v2_funct_1(X1) ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).

fof(f342,plain,
    ( spl3_25
    | spl3_15
    | ~ spl3_22
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(avatar_split_clause,[],[f337,f331,f238,f210,f280,f234,f339])).

fof(f234,plain,
    ( spl3_15
  <=> k1_xboole_0 = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f210,plain,
    ( spl3_14
  <=> k2_struct_0(sK1) = k2_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f238,plain,
    ( spl3_16
  <=> k2_struct_0(sK0) = k1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f331,plain,
    ( spl3_24
  <=> ! [X1,X0] :
        ( k1_xboole_0 = X0
        | ~ v1_funct_2(sK2,X1,X0)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | k2_relset_1(X1,X0,sK2) != X0
        | k6_partfun1(X1) = k5_relat_1(sK2,k2_funct_1(sK2)) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).

fof(f337,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2)
    | k6_partfun1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(trivial_inequality_removal,[],[f336])).

fof(f336,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2)
    | k6_partfun1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(forward_demodulation,[],[f334,f312])).

fof(f312,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f220,f310])).

fof(f310,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f106,f248])).

fof(f248,plain,
    ( u1_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f106,f240])).

fof(f240,plain,
    ( k2_struct_0(sK0) = k1_relat_1(sK2)
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f238])).

fof(f106,plain,(
    u1_struct_0(sK0) = k2_struct_0(sK0) ),
    inference(resolution,[],[f70,f57])).

fof(f57,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f55])).

fof(f55,plain,
    ( ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & ~ v2_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f54,f53,f52])).

fof(f52,plain,
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

fof(f53,plain,
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

fof(f54,plain,
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

fof(f23,plain,(
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
    inference(flattening,[],[f22])).

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
    inference(ennf_transformation,[],[f21])).

fof(f21,negated_conjecture,(
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
    inference(negated_conjecture,[],[f20])).

fof(f20,conjecture,(
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

fof(f70,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f24])).

fof(f24,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f17])).

fof(f17,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).

fof(f220,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_14 ),
    inference(backward_demodulation,[],[f113,f212])).

fof(f212,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f210])).

fof(f113,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f110,f107])).

fof(f107,plain,(
    u1_struct_0(sK1) = k2_struct_0(sK1) ),
    inference(resolution,[],[f70,f59])).

fof(f59,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f110,plain,(
    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(backward_demodulation,[],[f63,f106])).

fof(f63,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f334,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | k1_xboole_0 = k2_relat_1(sK2)
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | k6_partfun1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_24 ),
    inference(resolution,[],[f332,f313])).

fof(f313,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f221,f310])).

fof(f221,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_14 ),
    inference(backward_demodulation,[],[f114,f212])).

fof(f114,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f109,f107])).

fof(f109,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(backward_demodulation,[],[f62,f106])).

fof(f62,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f55])).

fof(f332,plain,
    ( ! [X0,X1] :
        ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        | ~ v1_funct_2(sK2,X1,X0)
        | k1_xboole_0 = X0
        | k2_relset_1(X1,X0,sK2) != X0
        | k6_partfun1(X1) = k5_relat_1(sK2,k2_funct_1(sK2)) )
    | ~ spl3_24 ),
    inference(avatar_component_clause,[],[f331])).

fof(f333,plain,
    ( ~ spl3_4
    | spl3_24 ),
    inference(avatar_split_clause,[],[f328,f331,f136])).

fof(f328,plain,(
    ! [X0,X1] :
      ( k1_xboole_0 = X0
      | k6_partfun1(X1) = k5_relat_1(sK2,k2_funct_1(sK2))
      | k2_relset_1(X1,X0,sK2) != X0
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v1_funct_2(sK2,X1,X0)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f92,f64])).

fof(f64,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f92,plain,(
    ! [X2,X0,X1] :
      ( ~ v2_funct_1(X2)
      | k1_xboole_0 = X1
      | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f47])).

fof(f47,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f46])).

fof(f46,plain,(
    ! [X0,X1,X2] :
      ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
        & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
      | k1_xboole_0 = X1
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f15])).

fof(f15,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_2(X2,X0,X1)
        & v1_funct_1(X2) )
     => ( ( v2_funct_1(X2)
          & k2_relset_1(X0,X1,X2) = X1 )
       => ( ( k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1)
            & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) )
          | k1_xboole_0 = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).

fof(f325,plain,
    ( ~ spl3_14
    | ~ spl3_16
    | spl3_21 ),
    inference(avatar_contradiction_clause,[],[f323])).

fof(f323,plain,
    ( $false
    | ~ spl3_14
    | ~ spl3_16
    | spl3_21 ),
    inference(resolution,[],[f278,f313])).

fof(f278,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | spl3_21 ),
    inference(avatar_component_clause,[],[f276])).

fof(f309,plain,
    ( spl3_2
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(avatar_contradiction_clause,[],[f308])).

fof(f308,plain,
    ( $false
    | spl3_2
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(resolution,[],[f302,f66])).

fof(f66,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnf_transformation,[],[f1])).

fof(f1,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

fof(f302,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | spl3_2
    | ~ spl3_14
    | ~ spl3_15 ),
    inference(backward_demodulation,[],[f223,f236])).

fof(f236,plain,
    ( k1_xboole_0 = k2_relat_1(sK2)
    | ~ spl3_15 ),
    inference(avatar_component_clause,[],[f234])).

fof(f223,plain,
    ( ~ v1_xboole_0(k2_relat_1(sK2))
    | spl3_2
    | ~ spl3_14 ),
    inference(backward_demodulation,[],[f125,f212])).

fof(f125,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | spl3_2 ),
    inference(avatar_component_clause,[],[f123])).

fof(f123,plain,
    ( spl3_2
  <=> v1_xboole_0(k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f306,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_22 ),
    inference(avatar_split_clause,[],[f289,f280,f136,f132])).

fof(f289,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_22 ),
    inference(resolution,[],[f282,f73])).

fof(f73,plain,(
    ! [X0] :
      ( v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f28,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f27])).

fof(f27,plain,(
    ! [X0] :
      ( ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f16])).

fof(f16,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
        & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0))
        & v1_funct_1(X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).

fof(f282,plain,
    ( ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | spl3_22 ),
    inference(avatar_component_clause,[],[f280])).

fof(f287,plain,
    ( ~ spl3_21
    | ~ spl3_22
    | ~ spl3_23
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f274,f269,f238,f210,f284,f280,f276])).

fof(f269,plain,
    ( spl3_20
  <=> ! [X1,X0] :
        ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1 ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f274,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_20 ),
    inference(trivial_inequality_removal,[],[f273])).

fof(f273,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_20 ),
    inference(forward_demodulation,[],[f272,f250])).

fof(f250,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f220,f240])).

fof(f272,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)
    | ~ v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))
    | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2)
    | ~ spl3_14
    | ~ spl3_16
    | ~ spl3_20 ),
    inference(superposition,[],[f249,f270])).

fof(f270,plain,
    ( ! [X0,X1] :
        ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
        | ~ v1_funct_2(sK2,X0,X1)
        | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | k2_relset_1(X0,X1,sK2) != X1 )
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f269])).

fof(f249,plain,
    ( ~ r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2)
    | ~ spl3_14
    | ~ spl3_16 ),
    inference(backward_demodulation,[],[f219,f240])).

fof(f219,plain,
    ( ~ r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2)
    | ~ spl3_14 ),
    inference(backward_demodulation,[],[f112,f212])).

fof(f112,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2) ),
    inference(backward_demodulation,[],[f111,f107])).

fof(f111,plain,(
    ~ r2_funct_2(k2_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(backward_demodulation,[],[f65,f106])).

fof(f65,plain,(
    ~ r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f271,plain,
    ( ~ spl3_4
    | spl3_20 ),
    inference(avatar_split_clause,[],[f266,f269,f136])).

fof(f266,plain,(
    ! [X0,X1] :
      ( k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2)
      | k2_relset_1(X0,X1,sK2) != X1
      | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(sK2,X0,X1)
      | ~ v1_funct_1(sK2) ) ),
    inference(resolution,[],[f91,f64])).

fof(f263,plain,
    ( ~ spl3_7
    | ~ spl3_8
    | ~ spl3_18
    | spl3_19
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f255,f153,f140,f261,f257,f166,f162])).

fof(f255,plain,
    ( ! [X0] :
        ( k2_relat_1(X0) != k2_relat_1(sK2)
        | k5_relat_1(X0,k2_funct_1(sK2)) != k6_partfun1(k1_relat_1(sK2))
        | k2_funct_1(k2_funct_1(sK2)) = X0
        | ~ v2_funct_1(k2_funct_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f254,f142])).

fof(f254,plain,
    ( ! [X0] :
        ( k5_relat_1(X0,k2_funct_1(sK2)) != k6_partfun1(k1_relat_1(sK2))
        | k2_funct_1(k2_funct_1(sK2)) = X0
        | k2_relat_1(X0) != k1_relat_1(k2_funct_1(sK2))
        | ~ v2_funct_1(k2_funct_1(sK2))
        | ~ v1_funct_1(X0)
        | ~ v1_relat_1(X0)
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ v1_relat_1(k2_funct_1(sK2)) )
    | ~ spl3_6 ),
    inference(superposition,[],[f99,f155])).

fof(f99,plain,(
    ! [X0,X1] :
      ( k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0))
      | k2_funct_1(X0) = X1
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(definition_unfolding,[],[f79,f67])).

fof(f79,plain,(
    ! [X0,X1] :
      ( k2_funct_1(X0) = X1
      | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
      | k2_relat_1(X1) != k1_relat_1(X0)
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X1)
      | ~ v1_relat_1(X1)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f34])).

fof(f34,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f33])).

fof(f33,plain,(
    ! [X0] :
      ( ! [X1] :
          ( k2_funct_1(X0) = X1
          | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0))
          | k2_relat_1(X1) != k1_relat_1(X0)
          | ~ v2_funct_1(X0)
          | ~ v1_funct_1(X1)
          | ~ v1_relat_1(X1) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ! [X1] :
          ( ( v1_funct_1(X1)
            & v1_relat_1(X1) )
         => ( ( k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0))
              & k2_relat_1(X1) = k1_relat_1(X0)
              & v2_funct_1(X0) )
           => k2_funct_1(X0) = X1 ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).

fof(f247,plain,
    ( ~ spl3_14
    | spl3_17 ),
    inference(avatar_contradiction_clause,[],[f246])).

fof(f246,plain,
    ( $false
    | ~ spl3_14
    | spl3_17 ),
    inference(resolution,[],[f244,f222])).

fof(f222,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ spl3_14 ),
    inference(backward_demodulation,[],[f115,f212])).

fof(f115,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f108,f107])).

fof(f108,plain,(
    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(backward_demodulation,[],[f61,f106])).

fof(f61,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f55])).

fof(f244,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | spl3_17 ),
    inference(avatar_component_clause,[],[f242])).

fof(f242,plain,
    ( spl3_17
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).

fof(f245,plain,
    ( ~ spl3_3
    | spl3_15
    | spl3_16
    | ~ spl3_4
    | ~ spl3_17
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f231,f210,f242,f136,f238,f234,f132])).

fof(f231,plain,
    ( ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | k2_struct_0(sK0) = k1_relat_1(sK2)
    | k1_xboole_0 = k2_relat_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_14 ),
    inference(resolution,[],[f228,f221])).

fof(f228,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) = X1
      | k1_xboole_0 = X2
      | ~ v1_relat_1(X0) ) ),
    inference(condensation,[],[f226])).

fof(f226,plain,(
    ! [X2,X0,X3,X1] :
      ( ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2)))
      | ~ v1_funct_2(X0,X1,X2)
      | ~ v1_funct_1(X0)
      | k1_relat_1(X0) = X1
      | k1_xboole_0 = X2
      | ~ v1_relat_1(X0)
      | ~ m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3))) ) ),
    inference(resolution,[],[f225,f86])).

fof(f86,plain,(
    ! [X2,X0,X1] :
      ( v4_relat_1(X2,X0)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f41])).

fof(f41,plain,(
    ! [X0,X1,X2] :
      ( ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => ( v5_relat_1(X2,X1)
        & v4_relat_1(X2,X0) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).

fof(f225,plain,(
    ! [X2,X0,X1] :
      ( ~ v4_relat_1(X1,X2)
      | ~ m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0)))
      | ~ v1_funct_2(X1,X2,X0)
      | ~ v1_funct_1(X1)
      | k1_relat_1(X1) = X2
      | k1_xboole_0 = X0
      | ~ v1_relat_1(X1) ) ),
    inference(resolution,[],[f104,f82])).

fof(f82,plain,(
    ! [X0,X1] :
      ( ~ v1_partfun1(X1,X0)
      | k1_relat_1(X1) = X0
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(cnf_transformation,[],[f56])).

fof(f56,plain,(
    ! [X0,X1] :
      ( ( ( v1_partfun1(X1,X0)
          | k1_relat_1(X1) != X0 )
        & ( k1_relat_1(X1) = X0
          | ~ v1_partfun1(X1,X0) ) )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(nnf_transformation,[],[f38])).

fof(f38,plain,(
    ! [X0,X1] :
      ( ( v1_partfun1(X1,X0)
      <=> k1_relat_1(X1) = X0 )
      | ~ v4_relat_1(X1,X0)
      | ~ v1_relat_1(X1) ) ),
    inference(flattening,[],[f37])).

fof(f37,plain,(
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

fof(f104,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(duplicate_literal_removal,[],[f94])).

fof(f94,plain,(
    ! [X2,X0,X1] :
      ( v1_partfun1(X2,X0)
      | k1_xboole_0 = X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f49])).

fof(f49,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f48])).

fof(f48,plain,(
    ! [X0,X1,X2] :
      ( v1_partfun1(X2,X0)
      | ( k1_xboole_0 != X0
        & k1_xboole_0 = X1 )
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f13])).

fof(f13,axiom,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X2) )
     => ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
          & v1_funct_2(X2,X0,X1)
          & v1_funct_1(X2) )
       => ( v1_partfun1(X2,X0)
          | ( k1_xboole_0 != X0
            & k1_xboole_0 = X1 ) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).

fof(f217,plain,(
    spl3_13 ),
    inference(avatar_contradiction_clause,[],[f216])).

fof(f216,plain,
    ( $false
    | spl3_13 ),
    inference(resolution,[],[f208,f114])).

fof(f208,plain,
    ( ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | spl3_13 ),
    inference(avatar_component_clause,[],[f206])).

fof(f206,plain,
    ( spl3_13
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f214,plain,
    ( ~ spl3_13
    | spl3_14 ),
    inference(avatar_split_clause,[],[f204,f210,f206])).

fof(f204,plain,
    ( k2_struct_0(sK1) = k2_relat_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    inference(superposition,[],[f113,f85])).

fof(f193,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_8 ),
    inference(avatar_split_clause,[],[f192,f166,f136,f132])).

fof(f192,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_8 ),
    inference(resolution,[],[f168,f76])).

fof(f76,plain,(
    ! [X0] :
      ( v1_funct_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f30,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f29])).

fof(f29,plain,(
    ! [X0] :
      ( ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) )
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v1_funct_1(k2_funct_1(X0))
        & v1_relat_1(k2_funct_1(X0)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).

fof(f168,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | spl3_8 ),
    inference(avatar_component_clause,[],[f166])).

fof(f191,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_7 ),
    inference(avatar_split_clause,[],[f189,f162,f136,f132])).

fof(f189,plain,
    ( ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | spl3_7 ),
    inference(resolution,[],[f164,f75])).

fof(f75,plain,(
    ! [X0] :
      ( v1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f30])).

fof(f164,plain,
    ( ~ v1_relat_1(k2_funct_1(sK2))
    | spl3_7 ),
    inference(avatar_component_clause,[],[f162])).

fof(f188,plain,
    ( ~ spl3_7
    | ~ spl3_8
    | spl3_12
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f183,f153,f140,f185,f166,f162])).

fof(f183,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f159,f155])).

fof(f159,plain,
    ( v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_5 ),
    inference(superposition,[],[f73,f142])).

fof(f173,plain,
    ( ~ spl3_7
    | ~ spl3_8
    | spl3_9
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(avatar_split_clause,[],[f160,f153,f140,f170,f166,f162])).

fof(f160,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_5
    | ~ spl3_6 ),
    inference(forward_demodulation,[],[f157,f155])).

fof(f157,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2)))))
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ v1_relat_1(k2_funct_1(sK2))
    | ~ spl3_5 ),
    inference(superposition,[],[f74,f142])).

fof(f74,plain,(
    ! [X0] :
      ( m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0))))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f28])).

fof(f156,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_6 ),
    inference(avatar_split_clause,[],[f147,f153,f136,f132])).

fof(f147,plain,
    ( k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f78,f64])).

fof(f78,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f32,plain,(
    ! [X0] :
      ( ( k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0))
        & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f31])).

fof(f31,plain,(
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
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).

fof(f151,plain,(
    spl3_3 ),
    inference(avatar_contradiction_clause,[],[f149])).

fof(f149,plain,
    ( $false
    | spl3_3 ),
    inference(resolution,[],[f144,f114])).

fof(f144,plain,
    ( ! [X0,X1] : ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
    | spl3_3 ),
    inference(resolution,[],[f134,f84])).

fof(f84,plain,(
    ! [X2,X0,X1] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(cnf_transformation,[],[f39])).

fof(f39,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f134,plain,
    ( ~ v1_relat_1(sK2)
    | spl3_3 ),
    inference(avatar_component_clause,[],[f132])).

fof(f146,plain,(
    spl3_4 ),
    inference(avatar_contradiction_clause,[],[f145])).

fof(f145,plain,
    ( $false
    | spl3_4 ),
    inference(resolution,[],[f138,f60])).

fof(f60,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f55])).

fof(f138,plain,
    ( ~ v1_funct_1(sK2)
    | spl3_4 ),
    inference(avatar_component_clause,[],[f136])).

fof(f143,plain,
    ( ~ spl3_3
    | ~ spl3_4
    | spl3_5 ),
    inference(avatar_split_clause,[],[f129,f140,f136,f132])).

fof(f129,plain,
    ( k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2) ),
    inference(resolution,[],[f77,f64])).

fof(f77,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f32])).

fof(f128,plain,(
    spl3_1 ),
    inference(avatar_contradiction_clause,[],[f127])).

fof(f127,plain,
    ( $false
    | spl3_1 ),
    inference(resolution,[],[f121,f59])).

fof(f121,plain,
    ( ~ l1_struct_0(sK1)
    | spl3_1 ),
    inference(avatar_component_clause,[],[f119])).

fof(f119,plain,
    ( spl3_1
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f126,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f117,f123,f119])).

fof(f117,plain,
    ( ~ v1_xboole_0(k2_struct_0(sK1))
    | ~ l1_struct_0(sK1) ),
    inference(forward_demodulation,[],[f116,f107])).

fof(f116,plain,
    ( ~ l1_struct_0(sK1)
    | ~ v1_xboole_0(u1_struct_0(sK1)) ),
    inference(resolution,[],[f71,f58])).

fof(f58,plain,(
    ~ v2_struct_0(sK1) ),
    inference(cnf_transformation,[],[f55])).

fof(f71,plain,(
    ! [X0] :
      ( v2_struct_0(X0)
      | ~ l1_struct_0(X0)
      | ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    inference(cnf_transformation,[],[f26])).

fof(f26,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(flattening,[],[f25])).

fof(f25,plain,(
    ! [X0] :
      ( ~ v1_xboole_0(u1_struct_0(X0))
      | ~ l1_struct_0(X0)
      | v2_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f18])).

fof(f18,axiom,(
    ! [X0] :
      ( ( l1_struct_0(X0)
        & ~ v2_struct_0(X0) )
     => ~ v1_xboole_0(u1_struct_0(X0)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : run_vampire %s %d
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % WCLimit    : 600
% 0.14/0.34  % DateTime   : Tue Dec  1 11:52:59 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.50  % (24130)ott+1002_8:1_add=off:afr=on:afp=100000:afq=1.1:amm=off:anc=none:bd=off:bs=unit_only:fsr=off:gs=on:gsem=off:nm=32:nwc=10:sas=z3:sp=occurrence:urr=on:updr=off_14 on theBenchmark
% 0.21/0.51  % (24114)dis+2_2:1_aac=none:afp=100000:afq=1.1:amm=sco:anc=none:bsr=on:fsr=off:gs=on:gsem=on:lcm=reverse:lma=on:nm=64:nwc=1:sos=on_6 on theBenchmark
% 0.21/0.51  % (24117)lrs+11_128_av=off:bsr=on:cond=on:gs=on:lcm=reverse:lma=on:nm=32:nwc=1:stl=30:sd=5:ss=axioms:st=3.0_1 on theBenchmark
% 0.21/0.51  % (24113)lrs+2_3:1_add=large:afr=on:afp=10000:afq=1.1:amm=off:anc=none:er=known:fde=unused:gs=on:gsaa=from_current:gsem=on:lma=on:nm=32:newcnf=on:nwc=4:sas=z3:stl=30:sd=1:ss=axioms:st=5.0:sac=on:sp=occurrence:updr=off_2 on theBenchmark
% 0.21/0.52  % (24118)ott+11_16_av=off:gs=on:gsem=on:irw=on:lma=on:nm=64:newcnf=on:nwc=1.3:sas=z3:sp=reverse_arity_14 on theBenchmark
% 0.21/0.52  % (24133)dis+1011_10_av=off:cond=on:lma=on:nm=0:newcnf=on:nwc=1:sos=on:sp=occurrence:updr=off_4 on theBenchmark
% 0.21/0.52  % (24112)lrs-11_12_av=off:nm=32:nwc=1.3:stl=30:sd=3:ss=axioms:sos=all_2 on theBenchmark
% 0.21/0.52  % (24124)lrs+1011_7_add=large:afr=on:afp=40000:afq=1.4:amm=off:anc=none:cond=on:er=known:fsr=off:lma=on:nm=4:nwc=2.5:stl=30:sp=reverse_arity:updr=off_2 on theBenchmark
% 0.21/0.52  % (24135)ott+4_40_av=off:bce=on:cond=fast:fde=none:nm=0:nwc=1:sos=all:updr=off_197 on theBenchmark
% 1.25/0.52  % (24127)lrs+1011_3:1_add=off:afr=on:afp=10000:afq=1.1:amm=off:bce=on:cond=on:ep=R:fsr=off:nm=16:nwc=1:stl=30:sos=all:sp=reverse_arity:updr=off_9 on theBenchmark
% 1.25/0.52  % (24121)lrs+11_1_add=large:afr=on:afp=100000:afq=2.0:amm=off:anc=none:bd=off:gs=on:gsem=on:irw=on:nm=32:newcnf=on:nwc=2.5:nicw=on:stl=30:sd=3:ss=axioms:sos=all:urr=on_34 on theBenchmark
% 1.25/0.52  % (24125)lrs+10_4:1_add=large:afp=100000:afq=1.1:anc=none:ep=RST:fde=unused:gsp=input_only:nm=6:newcnf=on:nwc=1:stl=30:sos=all:sac=on:sp=reverse_arity:urr=ec_only_22 on theBenchmark
% 1.25/0.52  % (24134)dis+1002_7_acc=on:afp=4000:afq=2.0:amm=sco:anc=none:cond=fast:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:nicw=on:sos=on:sac=on:sp=reverse_arity:urr=ec_only:updr=off_8 on theBenchmark
% 1.25/0.52  % (24128)dis+1_2:3_acc=on:add=large:afp=40000:afq=2.0:amm=sco:anc=none:er=filter:fsr=off:gsp=input_only:gs=on:gsem=off:nm=64:newcnf=on:nwc=1_3 on theBenchmark
% 1.25/0.52  % (24122)lrs+1003_3_awrs=decay:awrsf=4:add=large:afr=on:afp=100000:afq=2.0:amm=sco:bd=off:cond=fast:fsr=off:fde=unused:gs=on:gsem=on:nm=6:nwc=1:stl=30:sd=1:ss=axioms:st=1.2:sos=on:sac=on:sp=frequency:urr=on:updr=off_2 on theBenchmark
% 1.25/0.53  % (24129)ott+11_4_afp=100000:afq=1.2:amm=sco:anc=none:cond=fast:ep=R:fde=none:gs=on:gsaa=from_current:gsem=off:lma=on:nm=16:nwc=1:sd=3:ss=axioms:updr=off_2 on theBenchmark
% 1.25/0.53  % (24119)lrs+11_20_av=off:bs=unit_only:bsr=on:bce=on:cond=on:fde=none:gs=on:gsem=on:irw=on:nm=4:nwc=1:stl=30:sos=theory:sp=reverse_arity:uhcvi=on_3 on theBenchmark
% 1.25/0.53  % (24141)dis+1010_3:2_av=off:gsp=input_only:nm=2:nwc=1:sp=reverse_arity:urr=ec_only_29 on theBenchmark
% 1.25/0.53  % (24138)lrs+1011_8:1_afr=on:afp=1000:afq=2.0:br=off:gsp=input_only:gs=on:nm=16:nwc=1:stl=30:sos=all:sp=occurrence:urr=on_8 on theBenchmark
% 1.25/0.53  % (24132)lrs+1011_5:4_acc=on:add=large:afr=on:afp=10000:afq=2.0:amm=sco:anc=none:bsr=on:ccuc=first:cond=on:fde=unused:gs=on:gsaa=from_current:gsem=off:irw=on:nm=2:newcnf=on:nwc=1.2:stl=30:sos=on:sac=on:sp=reverse_arity:updr=off_126 on theBenchmark
% 1.25/0.53  % (24139)dis+1002_6_add=large:afp=40000:afq=2.0:bsr=on:cond=on:irw=on:lma=on:nm=2:nwc=2.5:nicw=on:sp=reverse_arity:updr=off_10 on theBenchmark
% 1.25/0.53  % (24122)Refutation not found, incomplete strategy% (24122)------------------------------
% 1.25/0.53  % (24122)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.25/0.53  % (24126)lrs+1010_8_add=off:afp=100000:afq=1.0:amm=off:anc=none:bce=on:irw=on:nm=16:newcnf=on:nwc=1.1:nicw=on:sas=z3:stl=30:sp=reverse_arity:urr=on_13 on theBenchmark
% 1.25/0.53  % (24122)Termination reason: Refutation not found, incomplete strategy
% 1.25/0.53  
% 1.25/0.53  % (24122)Memory used [KB]: 10746
% 1.25/0.53  % (24122)Time elapsed: 0.111 s
% 1.25/0.53  % (24122)------------------------------
% 1.25/0.53  % (24122)------------------------------
% 1.25/0.54  % (24137)dis+1_3:2_acc=on:add=off:afr=on:afp=40000:afq=1.0:amm=sco:anc=none:ccuc=small_ones:cond=on:lma=on:nm=64:nwc=1.3:sos=all:urr=on_111 on theBenchmark
% 1.38/0.54  % (24120)ott+2_2_afp=10000:afq=1.4:amm=off:anc=none:gsp=input_only:gs=on:gsem=off:irw=on:lcm=predicate:nm=32:nwc=1.5:sos=on:sp=reverse_arity_18 on theBenchmark
% 1.38/0.54  % (24116)lrs+1011_5_add=large:afp=1000:afq=1.2:anc=none:fsr=off:irw=on:lma=on:nm=64:newcnf=on:nwc=1:stl=30:sd=3:ss=axioms:st=2.0:sos=on:sac=on:sp=reverse_arity:urr=on:updr=off_10 on theBenchmark
% 1.38/0.55  % (24129)Refutation not found, incomplete strategy% (24129)------------------------------
% 1.38/0.55  % (24129)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.55  % (24140)lrs+11_4:1_aac=none:add=large:afr=on:afp=10000:afq=1.0:amm=sco:anc=none:cond=on:er=filter:fsr=off:gsp=input_only:gs=on:gsem=on:lma=on:nm=6:newcnf=on:nwc=1.1:sas=z3:stl=30:sos=theory:sp=reverse_arity:updr=off_3 on theBenchmark
% 1.38/0.55  % (24136)lrs+1010_3_av=off:fsr=off:gs=on:gsem=off:nm=2:newcnf=on:nwc=2:stl=30:sp=reverse_arity:urr=on:updr=off_9 on theBenchmark
% 1.38/0.56  % (24115)dis+1011_24_add=large:afr=on:afp=4000:afq=1.0:anc=none:bs=unit_only:bce=on:cond=fast:gs=on:nm=32:nwc=2.5:nicw=on:sp=occurrence:updr=off_39 on theBenchmark
% 1.38/0.56  % (24129)Termination reason: Refutation not found, incomplete strategy
% 1.38/0.56  
% 1.38/0.56  % (24129)Memory used [KB]: 10746
% 1.38/0.56  % (24129)Time elapsed: 0.121 s
% 1.38/0.56  % (24129)------------------------------
% 1.38/0.56  % (24129)------------------------------
% 1.38/0.56  % (24124)Refutation found. Thanks to Tanya!
% 1.38/0.56  % SZS status Theorem for theBenchmark
% 1.38/0.56  % SZS output start Proof for theBenchmark
% 1.38/0.56  fof(f568,plain,(
% 1.38/0.56    $false),
% 1.38/0.56    inference(avatar_sat_refutation,[],[f126,f128,f143,f146,f151,f156,f173,f188,f191,f193,f214,f217,f245,f247,f263,f271,f287,f306,f309,f325,f333,f342,f355,f357,f369,f467,f557,f559,f565])).
% 1.38/0.56  fof(f565,plain,(
% 1.38/0.56    ~spl3_6 | ~spl3_9 | spl3_50),
% 1.38/0.56    inference(avatar_contradiction_clause,[],[f563])).
% 1.38/0.56  fof(f563,plain,(
% 1.38/0.56    $false | (~spl3_6 | ~spl3_9 | spl3_50)),
% 1.38/0.56    inference(resolution,[],[f562,f172])).
% 1.38/0.56  fof(f172,plain,(
% 1.38/0.56    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~spl3_9),
% 1.38/0.56    inference(avatar_component_clause,[],[f170])).
% 1.38/0.56  fof(f170,plain,(
% 1.38/0.56    spl3_9 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2))))),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 1.38/0.56  fof(f562,plain,(
% 1.38/0.56    ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_6 | spl3_50)),
% 1.38/0.56    inference(trivial_inequality_removal,[],[f561])).
% 1.38/0.56  fof(f561,plain,(
% 1.38/0.56    k1_relat_1(sK2) != k1_relat_1(sK2) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | (~spl3_6 | spl3_50)),
% 1.38/0.56    inference(forward_demodulation,[],[f560,f155])).
% 1.38/0.56  fof(f155,plain,(
% 1.38/0.56    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~spl3_6),
% 1.38/0.56    inference(avatar_component_clause,[],[f153])).
% 1.38/0.56  fof(f153,plain,(
% 1.38/0.56    spl3_6 <=> k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2))),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 1.38/0.56  fof(f560,plain,(
% 1.38/0.56    k1_relat_1(sK2) != k2_relat_1(k2_funct_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | spl3_50),
% 1.38/0.56    inference(superposition,[],[f552,f85])).
% 1.38/0.56  fof(f85,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.38/0.56    inference(cnf_transformation,[],[f40])).
% 1.38/0.56  fof(f40,plain,(
% 1.38/0.56    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.56    inference(ennf_transformation,[],[f9])).
% 1.38/0.56  fof(f9,axiom,(
% 1.38/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 1.38/0.56  fof(f552,plain,(
% 1.38/0.56    k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | spl3_50),
% 1.38/0.56    inference(avatar_component_clause,[],[f550])).
% 1.38/0.56  fof(f550,plain,(
% 1.38/0.56    spl3_50 <=> k1_relat_1(sK2) = k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2))),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_50])])).
% 1.38/0.56  fof(f559,plain,(
% 1.38/0.56    ~spl3_4 | ~spl3_22 | ~spl3_21 | spl3_51),
% 1.38/0.56    inference(avatar_split_clause,[],[f558,f554,f276,f280,f136])).
% 1.38/0.56  fof(f136,plain,(
% 1.38/0.56    spl3_4 <=> v1_funct_1(sK2)),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 1.38/0.56  fof(f280,plain,(
% 1.38/0.56    spl3_22 <=> v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2))),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 1.38/0.56  fof(f276,plain,(
% 1.38/0.56    spl3_21 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2))))),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 1.38/0.56  fof(f554,plain,(
% 1.38/0.56    spl3_51 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2)),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_51])])).
% 1.38/0.56  fof(f558,plain,(
% 1.38/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | spl3_51),
% 1.38/0.56    inference(resolution,[],[f556,f103])).
% 1.38/0.56  fof(f103,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (r2_funct_2(X1,X2,X0,X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0)) )),
% 1.38/0.56    inference(duplicate_literal_removal,[],[f102])).
% 1.38/0.56  fof(f102,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | r2_funct_2(X1,X2,X0,X0) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0)) )),
% 1.38/0.56    inference(condensation,[],[f96])).
% 1.38/0.56  fof(f96,plain,(
% 1.38/0.56    ( ! [X2,X0,X3,X1] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f51])).
% 1.38/0.56  fof(f51,plain,(
% 1.38/0.56    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | ~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.38/0.56    inference(flattening,[],[f50])).
% 1.38/0.56  fof(f50,plain,(
% 1.38/0.56    ! [X0,X1,X2,X3] : (r2_funct_2(X0,X1,X2,X2) | (~m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X3,X0,X1) | ~v1_funct_1(X3) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.38/0.56    inference(ennf_transformation,[],[f12])).
% 1.38/0.56  fof(f12,axiom,(
% 1.38/0.56    ! [X0,X1,X2,X3] : ((m1_subset_1(X3,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X3,X0,X1) & v1_funct_1(X3) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => r2_funct_2(X0,X1,X2,X2))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',reflexivity_r2_funct_2)).
% 1.38/0.56  fof(f556,plain,(
% 1.38/0.56    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | spl3_51),
% 1.38/0.56    inference(avatar_component_clause,[],[f554])).
% 1.38/0.56  fof(f557,plain,(
% 1.38/0.56    ~spl3_50 | ~spl3_9 | ~spl3_12 | ~spl3_51 | spl3_23 | ~spl3_28 | ~spl3_43),
% 1.38/0.56    inference(avatar_split_clause,[],[f548,f464,f367,f284,f554,f185,f170,f550])).
% 1.38/0.56  fof(f185,plain,(
% 1.38/0.56    spl3_12 <=> v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2))),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 1.38/0.56  fof(f284,plain,(
% 1.38/0.56    spl3_23 <=> r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2)),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_23])])).
% 1.38/0.56  fof(f367,plain,(
% 1.38/0.56    spl3_28 <=> ! [X3,X2] : (k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X2,X3,k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),X2,X3) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k2_relset_1(X2,X3,k2_funct_1(sK2)) != X3)),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_28])])).
% 1.38/0.56  fof(f464,plain,(
% 1.38/0.56    spl3_43 <=> sK2 = k2_funct_1(k2_funct_1(sK2))),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_43])])).
% 1.38/0.56  fof(f548,plain,(
% 1.38/0.56    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2,sK2) | ~v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | k1_relat_1(sK2) != k2_relset_1(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)) | (spl3_23 | ~spl3_28 | ~spl3_43)),
% 1.38/0.56    inference(superposition,[],[f286,f470])).
% 1.38/0.56  fof(f470,plain,(
% 1.38/0.56    ( ! [X2,X3] : (sK2 = k2_tops_2(X2,X3,k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),X2,X3) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k2_relset_1(X2,X3,k2_funct_1(sK2)) != X3) ) | (~spl3_28 | ~spl3_43)),
% 1.38/0.56    inference(backward_demodulation,[],[f368,f466])).
% 1.38/0.56  fof(f466,plain,(
% 1.38/0.56    sK2 = k2_funct_1(k2_funct_1(sK2)) | ~spl3_43),
% 1.38/0.56    inference(avatar_component_clause,[],[f464])).
% 1.38/0.56  fof(f368,plain,(
% 1.38/0.56    ( ! [X2,X3] : (k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X2,X3,k2_funct_1(sK2)) | ~v1_funct_2(k2_funct_1(sK2),X2,X3) | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k2_relset_1(X2,X3,k2_funct_1(sK2)) != X3) ) | ~spl3_28),
% 1.38/0.56    inference(avatar_component_clause,[],[f367])).
% 1.38/0.56  fof(f286,plain,(
% 1.38/0.56    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) | spl3_23),
% 1.38/0.56    inference(avatar_component_clause,[],[f284])).
% 1.38/0.56  fof(f467,plain,(
% 1.38/0.56    spl3_43 | ~spl3_4 | ~spl3_3 | ~spl3_19 | ~spl3_25),
% 1.38/0.56    inference(avatar_split_clause,[],[f462,f339,f261,f132,f136,f464])).
% 1.38/0.56  fof(f132,plain,(
% 1.38/0.56    spl3_3 <=> v1_relat_1(sK2)),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 1.38/0.56  fof(f261,plain,(
% 1.38/0.56    spl3_19 <=> ! [X0] : (k2_relat_1(X0) != k2_relat_1(sK2) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k2_funct_1(k2_funct_1(sK2)) = X0 | k5_relat_1(X0,k2_funct_1(sK2)) != k6_partfun1(k1_relat_1(sK2)))),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 1.38/0.56  fof(f339,plain,(
% 1.38/0.56    spl3_25 <=> k6_partfun1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2))),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_25])])).
% 1.38/0.56  fof(f462,plain,(
% 1.38/0.56    ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2)) | (~spl3_19 | ~spl3_25)),
% 1.38/0.56    inference(trivial_inequality_removal,[],[f461])).
% 1.38/0.56  fof(f461,plain,(
% 1.38/0.56    k6_partfun1(k1_relat_1(sK2)) != k6_partfun1(k1_relat_1(sK2)) | ~v1_relat_1(sK2) | ~v1_funct_1(sK2) | sK2 = k2_funct_1(k2_funct_1(sK2)) | k2_relat_1(sK2) != k2_relat_1(sK2) | (~spl3_19 | ~spl3_25)),
% 1.38/0.56    inference(superposition,[],[f262,f341])).
% 1.38/0.56  fof(f341,plain,(
% 1.38/0.56    k6_partfun1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) | ~spl3_25),
% 1.38/0.56    inference(avatar_component_clause,[],[f339])).
% 1.38/0.56  fof(f262,plain,(
% 1.38/0.56    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(sK2)) != k6_partfun1(k1_relat_1(sK2)) | ~v1_relat_1(X0) | ~v1_funct_1(X0) | k2_funct_1(k2_funct_1(sK2)) = X0 | k2_relat_1(X0) != k2_relat_1(sK2)) ) | ~spl3_19),
% 1.38/0.56    inference(avatar_component_clause,[],[f261])).
% 1.38/0.56  fof(f369,plain,(
% 1.38/0.56    ~spl3_8 | spl3_28 | ~spl3_18),
% 1.38/0.56    inference(avatar_split_clause,[],[f359,f257,f367,f166])).
% 1.38/0.56  fof(f166,plain,(
% 1.38/0.56    spl3_8 <=> v1_funct_1(k2_funct_1(sK2))),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 1.38/0.56  fof(f257,plain,(
% 1.38/0.56    spl3_18 <=> v2_funct_1(k2_funct_1(sK2))),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 1.38/0.56  fof(f359,plain,(
% 1.38/0.56    ( ! [X2,X3] : (k2_funct_1(k2_funct_1(sK2)) = k2_tops_2(X2,X3,k2_funct_1(sK2)) | k2_relset_1(X2,X3,k2_funct_1(sK2)) != X3 | ~m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_2(k2_funct_1(sK2),X2,X3) | ~v1_funct_1(k2_funct_1(sK2))) ) | ~spl3_18),
% 1.38/0.56    inference(resolution,[],[f258,f91])).
% 1.38/0.56  fof(f91,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f45])).
% 1.38/0.56  fof(f45,plain,(
% 1.38/0.56    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.38/0.56    inference(flattening,[],[f44])).
% 1.38/0.56  fof(f44,plain,(
% 1.38/0.56    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.38/0.56    inference(ennf_transformation,[],[f19])).
% 1.38/0.56  fof(f19,axiom,(
% 1.38/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_tops_2)).
% 1.38/0.56  fof(f258,plain,(
% 1.38/0.56    v2_funct_1(k2_funct_1(sK2)) | ~spl3_18),
% 1.38/0.56    inference(avatar_component_clause,[],[f257])).
% 1.38/0.56  fof(f357,plain,(
% 1.38/0.56    spl3_26),
% 1.38/0.56    inference(avatar_contradiction_clause,[],[f356])).
% 1.38/0.56  fof(f356,plain,(
% 1.38/0.56    $false | spl3_26),
% 1.38/0.56    inference(resolution,[],[f354,f97])).
% 1.38/0.56  fof(f97,plain,(
% 1.38/0.56    ( ! [X0] : (v2_funct_1(k6_partfun1(X0))) )),
% 1.38/0.56    inference(definition_unfolding,[],[f69,f67])).
% 1.38/0.56  fof(f67,plain,(
% 1.38/0.56    ( ! [X0] : (k6_relat_1(X0) = k6_partfun1(X0)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f11])).
% 1.38/0.56  fof(f11,axiom,(
% 1.38/0.56    ! [X0] : k6_relat_1(X0) = k6_partfun1(X0)),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 1.38/0.56  fof(f69,plain,(
% 1.38/0.56    ( ! [X0] : (v2_funct_1(k6_relat_1(X0))) )),
% 1.38/0.56    inference(cnf_transformation,[],[f3])).
% 1.38/0.56  fof(f3,axiom,(
% 1.38/0.56    ! [X0] : (v2_funct_1(k6_relat_1(X0)) & v1_relat_1(k6_relat_1(X0)))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc4_funct_1)).
% 1.38/0.56  fof(f354,plain,(
% 1.38/0.56    ~v2_funct_1(k6_partfun1(k1_relat_1(sK2))) | spl3_26),
% 1.38/0.56    inference(avatar_component_clause,[],[f352])).
% 1.38/0.56  fof(f352,plain,(
% 1.38/0.56    spl3_26 <=> v2_funct_1(k6_partfun1(k1_relat_1(sK2)))),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 1.38/0.56  fof(f355,plain,(
% 1.38/0.56    ~spl3_7 | ~spl3_8 | ~spl3_3 | ~spl3_4 | spl3_18 | ~spl3_26 | ~spl3_5 | ~spl3_25),
% 1.38/0.56    inference(avatar_split_clause,[],[f350,f339,f140,f352,f257,f136,f132,f166,f162])).
% 1.38/0.56  fof(f162,plain,(
% 1.38/0.56    spl3_7 <=> v1_relat_1(k2_funct_1(sK2))),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 1.38/0.56  fof(f140,plain,(
% 1.38/0.56    spl3_5 <=> k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2))),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 1.38/0.56  fof(f350,plain,(
% 1.38/0.56    ~v2_funct_1(k6_partfun1(k1_relat_1(sK2))) | v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_5 | ~spl3_25)),
% 1.38/0.56    inference(trivial_inequality_removal,[],[f349])).
% 1.38/0.56  fof(f349,plain,(
% 1.38/0.56    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v2_funct_1(k6_partfun1(k1_relat_1(sK2))) | v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_5 | ~spl3_25)),
% 1.38/0.56    inference(forward_demodulation,[],[f347,f142])).
% 1.38/0.56  fof(f142,plain,(
% 1.38/0.56    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~spl3_5),
% 1.38/0.56    inference(avatar_component_clause,[],[f140])).
% 1.38/0.56  fof(f347,plain,(
% 1.38/0.56    ~v2_funct_1(k6_partfun1(k1_relat_1(sK2))) | k2_relat_1(sK2) != k1_relat_1(k2_funct_1(sK2)) | v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_25),
% 1.38/0.56    inference(superposition,[],[f81,f341])).
% 1.38/0.56  fof(f81,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~v2_funct_1(k5_relat_1(X1,X0)) | k2_relat_1(X1) != k1_relat_1(X0) | v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f36])).
% 1.38/0.56  fof(f36,plain,(
% 1.38/0.56    ! [X0] : (! [X1] : ((v2_funct_1(X0) & v2_funct_1(X1)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.38/0.56    inference(flattening,[],[f35])).
% 1.38/0.56  fof(f35,plain,(
% 1.38/0.56    ! [X0] : (! [X1] : (((v2_funct_1(X0) & v2_funct_1(X1)) | (k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(k5_relat_1(X1,X0)))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.38/0.56    inference(ennf_transformation,[],[f4])).
% 1.38/0.56  fof(f4,axiom,(
% 1.38/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(k5_relat_1(X1,X0))) => (v2_funct_1(X0) & v2_funct_1(X1)))))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_funct_1)).
% 1.38/0.56  fof(f342,plain,(
% 1.38/0.56    spl3_25 | spl3_15 | ~spl3_22 | ~spl3_14 | ~spl3_16 | ~spl3_24),
% 1.38/0.56    inference(avatar_split_clause,[],[f337,f331,f238,f210,f280,f234,f339])).
% 1.38/0.56  fof(f234,plain,(
% 1.38/0.56    spl3_15 <=> k1_xboole_0 = k2_relat_1(sK2)),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 1.38/0.56  fof(f210,plain,(
% 1.38/0.56    spl3_14 <=> k2_struct_0(sK1) = k2_relat_1(sK2)),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 1.38/0.56  fof(f238,plain,(
% 1.38/0.56    spl3_16 <=> k2_struct_0(sK0) = k1_relat_1(sK2)),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 1.38/0.56  fof(f331,plain,(
% 1.38/0.56    spl3_24 <=> ! [X1,X0] : (k1_xboole_0 = X0 | ~v1_funct_2(sK2,X1,X0) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | k2_relset_1(X1,X0,sK2) != X0 | k6_partfun1(X1) = k5_relat_1(sK2,k2_funct_1(sK2)))),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_24])])).
% 1.38/0.56  fof(f337,plain,(
% 1.38/0.56    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2) | k6_partfun1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) | (~spl3_14 | ~spl3_16 | ~spl3_24)),
% 1.38/0.56    inference(trivial_inequality_removal,[],[f336])).
% 1.38/0.56  fof(f336,plain,(
% 1.38/0.56    k2_relat_1(sK2) != k2_relat_1(sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2) | k6_partfun1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) | (~spl3_14 | ~spl3_16 | ~spl3_24)),
% 1.38/0.56    inference(forward_demodulation,[],[f334,f312])).
% 1.38/0.56  fof(f312,plain,(
% 1.38/0.56    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_14 | ~spl3_16)),
% 1.38/0.56    inference(backward_demodulation,[],[f220,f310])).
% 1.38/0.56  fof(f310,plain,(
% 1.38/0.56    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_16),
% 1.38/0.56    inference(backward_demodulation,[],[f106,f248])).
% 1.38/0.56  fof(f248,plain,(
% 1.38/0.56    u1_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_16),
% 1.38/0.56    inference(backward_demodulation,[],[f106,f240])).
% 1.38/0.56  fof(f240,plain,(
% 1.38/0.56    k2_struct_0(sK0) = k1_relat_1(sK2) | ~spl3_16),
% 1.38/0.56    inference(avatar_component_clause,[],[f238])).
% 1.38/0.56  fof(f106,plain,(
% 1.38/0.56    u1_struct_0(sK0) = k2_struct_0(sK0)),
% 1.38/0.56    inference(resolution,[],[f70,f57])).
% 1.38/0.56  fof(f57,plain,(
% 1.38/0.56    l1_struct_0(sK0)),
% 1.38/0.56    inference(cnf_transformation,[],[f55])).
% 1.38/0.56  fof(f55,plain,(
% 1.38/0.56    ((~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1)) & l1_struct_0(sK0)),
% 1.38/0.56    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f23,f54,f53,f52])).
% 1.38/0.56  fof(f52,plain,(
% 1.38/0.56    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(sK0))),
% 1.38/0.56    introduced(choice_axiom,[])).
% 1.38/0.56  fof(f53,plain,(
% 1.38/0.56    ? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) => (? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1) & ~v2_struct_0(sK1))),
% 1.38/0.56    introduced(choice_axiom,[])).
% 1.38/0.56  fof(f54,plain,(
% 1.38/0.56    ? [X2] : (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => (~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 1.38/0.56    introduced(choice_axiom,[])).
% 1.38/0.56  fof(f23,plain,(
% 1.38/0.56    ? [X0] : (? [X1] : (? [X2] : (~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1) & ~v2_struct_0(X1)) & l1_struct_0(X0))),
% 1.38/0.56    inference(flattening,[],[f22])).
% 1.38/0.56  fof(f22,plain,(
% 1.38/0.56    ? [X0] : (? [X1] : (? [X2] : ((~r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & (l1_struct_0(X1) & ~v2_struct_0(X1))) & l1_struct_0(X0))),
% 1.38/0.56    inference(ennf_transformation,[],[f21])).
% 1.38/0.56  fof(f21,negated_conjecture,(
% 1.38/0.56    ~! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.38/0.56    inference(negated_conjecture,[],[f20])).
% 1.38/0.56  fof(f20,conjecture,(
% 1.38/0.56    ! [X0] : (l1_struct_0(X0) => ! [X1] : ((l1_struct_0(X1) & ~v2_struct_0(X1)) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => r2_funct_2(u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X1),u1_struct_0(X0),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)),X2)))))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_tops_2)).
% 1.38/0.56  fof(f70,plain,(
% 1.38/0.56    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f24])).
% 1.38/0.56  fof(f24,plain,(
% 1.38/0.56    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 1.38/0.56    inference(ennf_transformation,[],[f17])).
% 1.38/0.56  fof(f17,axiom,(
% 1.38/0.56    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_struct_0)).
% 1.38/0.56  fof(f220,plain,(
% 1.38/0.56    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_14),
% 1.38/0.56    inference(backward_demodulation,[],[f113,f212])).
% 1.38/0.56  fof(f212,plain,(
% 1.38/0.56    k2_struct_0(sK1) = k2_relat_1(sK2) | ~spl3_14),
% 1.38/0.56    inference(avatar_component_clause,[],[f210])).
% 1.38/0.56  fof(f113,plain,(
% 1.38/0.56    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 1.38/0.56    inference(backward_demodulation,[],[f110,f107])).
% 1.38/0.56  fof(f107,plain,(
% 1.38/0.56    u1_struct_0(sK1) = k2_struct_0(sK1)),
% 1.38/0.56    inference(resolution,[],[f70,f59])).
% 1.38/0.56  fof(f59,plain,(
% 1.38/0.56    l1_struct_0(sK1)),
% 1.38/0.56    inference(cnf_transformation,[],[f55])).
% 1.38/0.56  fof(f110,plain,(
% 1.38/0.56    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 1.38/0.56    inference(backward_demodulation,[],[f63,f106])).
% 1.38/0.56  fof(f63,plain,(
% 1.38/0.56    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 1.38/0.56    inference(cnf_transformation,[],[f55])).
% 1.38/0.56  fof(f334,plain,(
% 1.38/0.56    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | k1_xboole_0 = k2_relat_1(sK2) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | k6_partfun1(k1_relat_1(sK2)) = k5_relat_1(sK2,k2_funct_1(sK2)) | (~spl3_14 | ~spl3_16 | ~spl3_24)),
% 1.38/0.56    inference(resolution,[],[f332,f313])).
% 1.38/0.56  fof(f313,plain,(
% 1.38/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_14 | ~spl3_16)),
% 1.38/0.56    inference(backward_demodulation,[],[f221,f310])).
% 1.38/0.56  fof(f221,plain,(
% 1.38/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_14),
% 1.38/0.56    inference(backward_demodulation,[],[f114,f212])).
% 1.38/0.56  fof(f114,plain,(
% 1.38/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 1.38/0.56    inference(backward_demodulation,[],[f109,f107])).
% 1.38/0.56  fof(f109,plain,(
% 1.38/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),u1_struct_0(sK1))))),
% 1.38/0.56    inference(backward_demodulation,[],[f62,f106])).
% 1.38/0.56  fof(f62,plain,(
% 1.38/0.56    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 1.38/0.56    inference(cnf_transformation,[],[f55])).
% 1.38/0.56  fof(f332,plain,(
% 1.38/0.56    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK2,X1,X0) | k1_xboole_0 = X0 | k2_relset_1(X1,X0,sK2) != X0 | k6_partfun1(X1) = k5_relat_1(sK2,k2_funct_1(sK2))) ) | ~spl3_24),
% 1.38/0.56    inference(avatar_component_clause,[],[f331])).
% 1.38/0.56  fof(f333,plain,(
% 1.38/0.56    ~spl3_4 | spl3_24),
% 1.38/0.56    inference(avatar_split_clause,[],[f328,f331,f136])).
% 1.38/0.56  fof(f328,plain,(
% 1.38/0.56    ( ! [X0,X1] : (k1_xboole_0 = X0 | k6_partfun1(X1) = k5_relat_1(sK2,k2_funct_1(sK2)) | k2_relset_1(X1,X0,sK2) != X0 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v1_funct_2(sK2,X1,X0) | ~v1_funct_1(sK2)) )),
% 1.38/0.56    inference(resolution,[],[f92,f64])).
% 1.38/0.56  fof(f64,plain,(
% 1.38/0.56    v2_funct_1(sK2)),
% 1.38/0.56    inference(cnf_transformation,[],[f55])).
% 1.38/0.56  fof(f92,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (~v2_funct_1(X2) | k1_xboole_0 = X1 | k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2)) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f47])).
% 1.38/0.56  fof(f47,plain,(
% 1.38/0.56    ! [X0,X1,X2] : ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1 | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 1.38/0.56    inference(flattening,[],[f46])).
% 1.38/0.56  fof(f46,plain,(
% 1.38/0.56    ! [X0,X1,X2] : ((((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 1.38/0.56    inference(ennf_transformation,[],[f15])).
% 1.38/0.56  fof(f15,axiom,(
% 1.38/0.56    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => ((k5_relat_1(k2_funct_1(X2),X2) = k6_partfun1(X1) & k6_partfun1(X0) = k5_relat_1(X2,k2_funct_1(X2))) | k1_xboole_0 = X1)))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t35_funct_2)).
% 1.38/0.56  fof(f325,plain,(
% 1.38/0.56    ~spl3_14 | ~spl3_16 | spl3_21),
% 1.38/0.56    inference(avatar_contradiction_clause,[],[f323])).
% 1.38/0.56  fof(f323,plain,(
% 1.38/0.56    $false | (~spl3_14 | ~spl3_16 | spl3_21)),
% 1.38/0.56    inference(resolution,[],[f278,f313])).
% 1.38/0.56  fof(f278,plain,(
% 1.38/0.56    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | spl3_21),
% 1.38/0.56    inference(avatar_component_clause,[],[f276])).
% 1.38/0.56  fof(f309,plain,(
% 1.38/0.56    spl3_2 | ~spl3_14 | ~spl3_15),
% 1.38/0.56    inference(avatar_contradiction_clause,[],[f308])).
% 1.38/0.56  fof(f308,plain,(
% 1.38/0.56    $false | (spl3_2 | ~spl3_14 | ~spl3_15)),
% 1.38/0.56    inference(resolution,[],[f302,f66])).
% 1.38/0.56  fof(f66,plain,(
% 1.38/0.56    v1_xboole_0(k1_xboole_0)),
% 1.38/0.56    inference(cnf_transformation,[],[f1])).
% 1.38/0.56  fof(f1,axiom,(
% 1.38/0.56    v1_xboole_0(k1_xboole_0)),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).
% 1.38/0.56  fof(f302,plain,(
% 1.38/0.56    ~v1_xboole_0(k1_xboole_0) | (spl3_2 | ~spl3_14 | ~spl3_15)),
% 1.38/0.56    inference(backward_demodulation,[],[f223,f236])).
% 1.38/0.56  fof(f236,plain,(
% 1.38/0.56    k1_xboole_0 = k2_relat_1(sK2) | ~spl3_15),
% 1.38/0.56    inference(avatar_component_clause,[],[f234])).
% 1.38/0.56  fof(f223,plain,(
% 1.38/0.56    ~v1_xboole_0(k2_relat_1(sK2)) | (spl3_2 | ~spl3_14)),
% 1.38/0.56    inference(backward_demodulation,[],[f125,f212])).
% 1.38/0.56  fof(f125,plain,(
% 1.38/0.56    ~v1_xboole_0(k2_struct_0(sK1)) | spl3_2),
% 1.38/0.56    inference(avatar_component_clause,[],[f123])).
% 1.38/0.56  fof(f123,plain,(
% 1.38/0.56    spl3_2 <=> v1_xboole_0(k2_struct_0(sK1))),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 1.38/0.56  fof(f306,plain,(
% 1.38/0.56    ~spl3_3 | ~spl3_4 | spl3_22),
% 1.38/0.56    inference(avatar_split_clause,[],[f289,f280,f136,f132])).
% 1.38/0.56  fof(f289,plain,(
% 1.38/0.56    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_22),
% 1.38/0.56    inference(resolution,[],[f282,f73])).
% 1.38/0.56  fof(f73,plain,(
% 1.38/0.56    ( ! [X0] : (v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f28])).
% 1.38/0.56  fof(f28,plain,(
% 1.38/0.56    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.38/0.56    inference(flattening,[],[f27])).
% 1.38/0.56  fof(f27,plain,(
% 1.38/0.56    ! [X0] : ((m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.38/0.56    inference(ennf_transformation,[],[f16])).
% 1.38/0.56  fof(f16,axiom,(
% 1.38/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) & v1_funct_2(X0,k1_relat_1(X0),k2_relat_1(X0)) & v1_funct_1(X0)))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_funct_2)).
% 1.38/0.56  fof(f282,plain,(
% 1.38/0.56    ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | spl3_22),
% 1.38/0.56    inference(avatar_component_clause,[],[f280])).
% 1.38/0.56  fof(f287,plain,(
% 1.38/0.56    ~spl3_21 | ~spl3_22 | ~spl3_23 | ~spl3_14 | ~spl3_16 | ~spl3_20),
% 1.38/0.56    inference(avatar_split_clause,[],[f274,f269,f238,f210,f284,f280,f276])).
% 1.38/0.56  fof(f269,plain,(
% 1.38/0.56    spl3_20 <=> ! [X1,X0] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1)),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 1.38/0.56  fof(f274,plain,(
% 1.38/0.56    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_14 | ~spl3_16 | ~spl3_20)),
% 1.38/0.56    inference(trivial_inequality_removal,[],[f273])).
% 1.38/0.56  fof(f273,plain,(
% 1.38/0.56    k2_relat_1(sK2) != k2_relat_1(sK2) | ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | (~spl3_14 | ~spl3_16 | ~spl3_20)),
% 1.38/0.56    inference(forward_demodulation,[],[f272,f250])).
% 1.38/0.56  fof(f250,plain,(
% 1.38/0.56    k2_relat_1(sK2) = k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_14 | ~spl3_16)),
% 1.38/0.56    inference(backward_demodulation,[],[f220,f240])).
% 1.38/0.56  fof(f272,plain,(
% 1.38/0.56    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_funct_1(sK2)),sK2) | ~v1_funct_2(sK2,k1_relat_1(sK2),k2_relat_1(sK2)) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(sK2),k2_relat_1(sK2)))) | k2_relat_1(sK2) != k2_relset_1(k1_relat_1(sK2),k2_relat_1(sK2),sK2) | (~spl3_14 | ~spl3_16 | ~spl3_20)),
% 1.38/0.56    inference(superposition,[],[f249,f270])).
% 1.38/0.56  fof(f270,plain,(
% 1.38/0.56    ( ! [X0,X1] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | ~v1_funct_2(sK2,X0,X1) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,sK2) != X1) ) | ~spl3_20),
% 1.38/0.56    inference(avatar_component_clause,[],[f269])).
% 1.38/0.56  fof(f249,plain,(
% 1.38/0.56    ~r2_funct_2(k1_relat_1(sK2),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k1_relat_1(sK2),k2_tops_2(k1_relat_1(sK2),k2_relat_1(sK2),sK2)),sK2) | (~spl3_14 | ~spl3_16)),
% 1.38/0.56    inference(backward_demodulation,[],[f219,f240])).
% 1.38/0.56  fof(f219,plain,(
% 1.38/0.56    ~r2_funct_2(k2_struct_0(sK0),k2_relat_1(sK2),k2_tops_2(k2_relat_1(sK2),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),sK2) | ~spl3_14),
% 1.38/0.56    inference(backward_demodulation,[],[f112,f212])).
% 1.38/0.56  fof(f112,plain,(
% 1.38/0.56    ~r2_funct_2(k2_struct_0(sK0),k2_struct_0(sK1),k2_tops_2(k2_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),sK2)),
% 1.38/0.56    inference(backward_demodulation,[],[f111,f107])).
% 1.38/0.56  fof(f111,plain,(
% 1.38/0.56    ~r2_funct_2(k2_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),k2_struct_0(sK0),k2_tops_2(k2_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 1.38/0.56    inference(backward_demodulation,[],[f65,f106])).
% 1.38/0.56  fof(f65,plain,(
% 1.38/0.56    ~r2_funct_2(u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK1),u1_struct_0(sK0),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),sK2)),
% 1.38/0.56    inference(cnf_transformation,[],[f55])).
% 1.38/0.56  fof(f271,plain,(
% 1.38/0.56    ~spl3_4 | spl3_20),
% 1.38/0.56    inference(avatar_split_clause,[],[f266,f269,f136])).
% 1.38/0.56  fof(f266,plain,(
% 1.38/0.56    ( ! [X0,X1] : (k2_funct_1(sK2) = k2_tops_2(X0,X1,sK2) | k2_relset_1(X0,X1,sK2) != X1 | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(sK2,X0,X1) | ~v1_funct_1(sK2)) )),
% 1.38/0.56    inference(resolution,[],[f91,f64])).
% 1.38/0.56  fof(f263,plain,(
% 1.38/0.56    ~spl3_7 | ~spl3_8 | ~spl3_18 | spl3_19 | ~spl3_5 | ~spl3_6),
% 1.38/0.56    inference(avatar_split_clause,[],[f255,f153,f140,f261,f257,f166,f162])).
% 1.38/0.56  fof(f255,plain,(
% 1.38/0.56    ( ! [X0] : (k2_relat_1(X0) != k2_relat_1(sK2) | k5_relat_1(X0,k2_funct_1(sK2)) != k6_partfun1(k1_relat_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = X0 | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))) ) | (~spl3_5 | ~spl3_6)),
% 1.38/0.56    inference(forward_demodulation,[],[f254,f142])).
% 1.38/0.56  fof(f254,plain,(
% 1.38/0.56    ( ! [X0] : (k5_relat_1(X0,k2_funct_1(sK2)) != k6_partfun1(k1_relat_1(sK2)) | k2_funct_1(k2_funct_1(sK2)) = X0 | k2_relat_1(X0) != k1_relat_1(k2_funct_1(sK2)) | ~v2_funct_1(k2_funct_1(sK2)) | ~v1_funct_1(X0) | ~v1_relat_1(X0) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2))) ) | ~spl3_6),
% 1.38/0.56    inference(superposition,[],[f99,f155])).
% 1.38/0.56  fof(f99,plain,(
% 1.38/0.56    ( ! [X0,X1] : (k5_relat_1(X1,X0) != k6_partfun1(k2_relat_1(X0)) | k2_funct_1(X0) = X1 | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.38/0.56    inference(definition_unfolding,[],[f79,f67])).
% 1.38/0.56  fof(f79,plain,(
% 1.38/0.56    ( ! [X0,X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.38/0.56    inference(cnf_transformation,[],[f34])).
% 1.38/0.56  fof(f34,plain,(
% 1.38/0.56    ! [X0] : (! [X1] : (k2_funct_1(X0) = X1 | k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0) | ~v1_funct_1(X1) | ~v1_relat_1(X1)) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.38/0.56    inference(flattening,[],[f33])).
% 1.38/0.56  fof(f33,plain,(
% 1.38/0.56    ! [X0] : (! [X1] : ((k2_funct_1(X0) = X1 | (k5_relat_1(X1,X0) != k6_relat_1(k2_relat_1(X0)) | k2_relat_1(X1) != k1_relat_1(X0) | ~v2_funct_1(X0))) | (~v1_funct_1(X1) | ~v1_relat_1(X1))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.38/0.56    inference(ennf_transformation,[],[f6])).
% 1.38/0.56  fof(f6,axiom,(
% 1.38/0.56    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => ! [X1] : ((v1_funct_1(X1) & v1_relat_1(X1)) => ((k5_relat_1(X1,X0) = k6_relat_1(k2_relat_1(X0)) & k2_relat_1(X1) = k1_relat_1(X0) & v2_funct_1(X0)) => k2_funct_1(X0) = X1)))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_funct_1)).
% 1.38/0.56  fof(f247,plain,(
% 1.38/0.56    ~spl3_14 | spl3_17),
% 1.38/0.56    inference(avatar_contradiction_clause,[],[f246])).
% 1.38/0.56  fof(f246,plain,(
% 1.38/0.56    $false | (~spl3_14 | spl3_17)),
% 1.38/0.56    inference(resolution,[],[f244,f222])).
% 1.38/0.56  fof(f222,plain,(
% 1.38/0.56    v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~spl3_14),
% 1.38/0.56    inference(backward_demodulation,[],[f115,f212])).
% 1.38/0.56  fof(f115,plain,(
% 1.38/0.56    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 1.38/0.56    inference(backward_demodulation,[],[f108,f107])).
% 1.38/0.56  fof(f108,plain,(
% 1.38/0.56    v1_funct_2(sK2,k2_struct_0(sK0),u1_struct_0(sK1))),
% 1.38/0.56    inference(backward_demodulation,[],[f61,f106])).
% 1.38/0.56  fof(f61,plain,(
% 1.38/0.56    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 1.38/0.56    inference(cnf_transformation,[],[f55])).
% 1.38/0.56  fof(f244,plain,(
% 1.38/0.56    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | spl3_17),
% 1.38/0.56    inference(avatar_component_clause,[],[f242])).
% 1.38/0.56  fof(f242,plain,(
% 1.38/0.56    spl3_17 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 1.38/0.56    introduced(avatar_definition,[new_symbols(naming,[spl3_17])])).
% 1.38/0.56  fof(f245,plain,(
% 1.38/0.56    ~spl3_3 | spl3_15 | spl3_16 | ~spl3_4 | ~spl3_17 | ~spl3_14),
% 1.38/0.56    inference(avatar_split_clause,[],[f231,f210,f242,f136,f238,f234,f132])).
% 1.38/0.56  fof(f231,plain,(
% 1.38/0.56    ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | k2_struct_0(sK0) = k1_relat_1(sK2) | k1_xboole_0 = k2_relat_1(sK2) | ~v1_relat_1(sK2) | ~spl3_14),
% 1.38/0.56    inference(resolution,[],[f228,f221])).
% 1.38/0.56  fof(f228,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0) | k1_relat_1(X0) = X1 | k1_xboole_0 = X2 | ~v1_relat_1(X0)) )),
% 1.38/0.56    inference(condensation,[],[f226])).
% 1.38/0.56  fof(f226,plain,(
% 1.38/0.56    ( ! [X2,X0,X3,X1] : (~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X2))) | ~v1_funct_2(X0,X1,X2) | ~v1_funct_1(X0) | k1_relat_1(X0) = X1 | k1_xboole_0 = X2 | ~v1_relat_1(X0) | ~m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(X1,X3)))) )),
% 1.38/0.56    inference(resolution,[],[f225,f86])).
% 1.38/0.56  fof(f86,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (v4_relat_1(X2,X0) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.38/0.56    inference(cnf_transformation,[],[f41])).
% 1.38/0.56  fof(f41,plain,(
% 1.38/0.56    ! [X0,X1,X2] : ((v5_relat_1(X2,X1) & v4_relat_1(X2,X0)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.56    inference(ennf_transformation,[],[f8])).
% 1.38/0.56  fof(f8,axiom,(
% 1.38/0.56    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => (v5_relat_1(X2,X1) & v4_relat_1(X2,X0)))),
% 1.38/0.56    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc2_relset_1)).
% 1.38/0.56  fof(f225,plain,(
% 1.38/0.56    ( ! [X2,X0,X1] : (~v4_relat_1(X1,X2) | ~m1_subset_1(X1,k1_zfmisc_1(k2_zfmisc_1(X2,X0))) | ~v1_funct_2(X1,X2,X0) | ~v1_funct_1(X1) | k1_relat_1(X1) = X2 | k1_xboole_0 = X0 | ~v1_relat_1(X1)) )),
% 1.38/0.56    inference(resolution,[],[f104,f82])).
% 1.38/0.57  fof(f82,plain,(
% 1.38/0.57    ( ! [X0,X1] : (~v1_partfun1(X1,X0) | k1_relat_1(X1) = X0 | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f56])).
% 1.38/0.57  fof(f56,plain,(
% 1.38/0.57    ! [X0,X1] : (((v1_partfun1(X1,X0) | k1_relat_1(X1) != X0) & (k1_relat_1(X1) = X0 | ~v1_partfun1(X1,X0))) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.38/0.57    inference(nnf_transformation,[],[f38])).
% 1.38/0.57  fof(f38,plain,(
% 1.38/0.57    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | ~v4_relat_1(X1,X0) | ~v1_relat_1(X1))),
% 1.38/0.57    inference(flattening,[],[f37])).
% 1.38/0.57  fof(f37,plain,(
% 1.38/0.57    ! [X0,X1] : ((v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0) | (~v4_relat_1(X1,X0) | ~v1_relat_1(X1)))),
% 1.38/0.57    inference(ennf_transformation,[],[f10])).
% 1.38/0.57  fof(f10,axiom,(
% 1.38/0.57    ! [X0,X1] : ((v4_relat_1(X1,X0) & v1_relat_1(X1)) => (v1_partfun1(X1,X0) <=> k1_relat_1(X1) = X0))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_partfun1)).
% 1.38/0.57  fof(f104,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 1.38/0.57    inference(duplicate_literal_removal,[],[f94])).
% 1.38/0.57  fof(f94,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (v1_partfun1(X2,X0) | k1_xboole_0 = X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f49])).
% 1.38/0.57  fof(f49,plain,(
% 1.38/0.57    ! [X0,X1,X2] : (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2))),
% 1.38/0.57    inference(flattening,[],[f48])).
% 1.38/0.57  fof(f48,plain,(
% 1.38/0.57    ! [X0,X1,X2] : (((v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)))),
% 1.38/0.57    inference(ennf_transformation,[],[f13])).
% 1.38/0.57  fof(f13,axiom,(
% 1.38/0.57    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X2)) => ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => (v1_partfun1(X2,X0) | (k1_xboole_0 != X0 & k1_xboole_0 = X1))))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t132_funct_2)).
% 1.38/0.57  fof(f217,plain,(
% 1.38/0.57    spl3_13),
% 1.38/0.57    inference(avatar_contradiction_clause,[],[f216])).
% 1.38/0.57  fof(f216,plain,(
% 1.38/0.57    $false | spl3_13),
% 1.38/0.57    inference(resolution,[],[f208,f114])).
% 1.38/0.57  fof(f208,plain,(
% 1.38/0.57    ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | spl3_13),
% 1.38/0.57    inference(avatar_component_clause,[],[f206])).
% 1.38/0.57  fof(f206,plain,(
% 1.38/0.57    spl3_13 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 1.38/0.57  fof(f214,plain,(
% 1.38/0.57    ~spl3_13 | spl3_14),
% 1.38/0.57    inference(avatar_split_clause,[],[f204,f210,f206])).
% 1.38/0.57  fof(f204,plain,(
% 1.38/0.57    k2_struct_0(sK1) = k2_relat_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 1.38/0.57    inference(superposition,[],[f113,f85])).
% 1.38/0.57  fof(f193,plain,(
% 1.38/0.57    ~spl3_3 | ~spl3_4 | spl3_8),
% 1.38/0.57    inference(avatar_split_clause,[],[f192,f166,f136,f132])).
% 1.38/0.57  fof(f192,plain,(
% 1.38/0.57    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_8),
% 1.38/0.57    inference(resolution,[],[f168,f76])).
% 1.38/0.57  fof(f76,plain,(
% 1.38/0.57    ( ! [X0] : (v1_funct_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f30])).
% 1.38/0.57  fof(f30,plain,(
% 1.38/0.57    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.38/0.57    inference(flattening,[],[f29])).
% 1.38/0.57  fof(f29,plain,(
% 1.38/0.57    ! [X0] : ((v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.38/0.57    inference(ennf_transformation,[],[f2])).
% 1.38/0.57  fof(f2,axiom,(
% 1.38/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v1_funct_1(k2_funct_1(X0)) & v1_relat_1(k2_funct_1(X0))))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_k2_funct_1)).
% 1.38/0.57  fof(f168,plain,(
% 1.38/0.57    ~v1_funct_1(k2_funct_1(sK2)) | spl3_8),
% 1.38/0.57    inference(avatar_component_clause,[],[f166])).
% 1.38/0.57  fof(f191,plain,(
% 1.38/0.57    ~spl3_3 | ~spl3_4 | spl3_7),
% 1.38/0.57    inference(avatar_split_clause,[],[f189,f162,f136,f132])).
% 1.38/0.57  fof(f189,plain,(
% 1.38/0.57    ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | spl3_7),
% 1.38/0.57    inference(resolution,[],[f164,f75])).
% 1.38/0.57  fof(f75,plain,(
% 1.38/0.57    ( ! [X0] : (v1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f30])).
% 1.38/0.57  fof(f164,plain,(
% 1.38/0.57    ~v1_relat_1(k2_funct_1(sK2)) | spl3_7),
% 1.38/0.57    inference(avatar_component_clause,[],[f162])).
% 1.38/0.57  fof(f188,plain,(
% 1.38/0.57    ~spl3_7 | ~spl3_8 | spl3_12 | ~spl3_5 | ~spl3_6),
% 1.38/0.57    inference(avatar_split_clause,[],[f183,f153,f140,f185,f166,f162])).
% 1.38/0.57  fof(f183,plain,(
% 1.38/0.57    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k1_relat_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_5 | ~spl3_6)),
% 1.38/0.57    inference(forward_demodulation,[],[f159,f155])).
% 1.38/0.57  fof(f159,plain,(
% 1.38/0.57    v1_funct_2(k2_funct_1(sK2),k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_5),
% 1.38/0.57    inference(superposition,[],[f73,f142])).
% 1.38/0.57  fof(f173,plain,(
% 1.38/0.57    ~spl3_7 | ~spl3_8 | spl3_9 | ~spl3_5 | ~spl3_6),
% 1.38/0.57    inference(avatar_split_clause,[],[f160,f153,f140,f170,f166,f162])).
% 1.38/0.57  fof(f160,plain,(
% 1.38/0.57    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k1_relat_1(sK2)))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | (~spl3_5 | ~spl3_6)),
% 1.38/0.57    inference(forward_demodulation,[],[f157,f155])).
% 1.38/0.57  fof(f157,plain,(
% 1.38/0.57    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_relat_1(k2_funct_1(sK2))))) | ~v1_funct_1(k2_funct_1(sK2)) | ~v1_relat_1(k2_funct_1(sK2)) | ~spl3_5),
% 1.38/0.57    inference(superposition,[],[f74,f142])).
% 1.38/0.57  fof(f74,plain,(
% 1.38/0.57    ( ! [X0] : (m1_subset_1(X0,k1_zfmisc_1(k2_zfmisc_1(k1_relat_1(X0),k2_relat_1(X0)))) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f28])).
% 1.38/0.57  fof(f156,plain,(
% 1.38/0.57    ~spl3_3 | ~spl3_4 | spl3_6),
% 1.38/0.57    inference(avatar_split_clause,[],[f147,f153,f136,f132])).
% 1.38/0.57  fof(f147,plain,(
% 1.38/0.57    k1_relat_1(sK2) = k2_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.38/0.57    inference(resolution,[],[f78,f64])).
% 1.38/0.57  fof(f78,plain,(
% 1.38/0.57    ( ! [X0] : (~v2_funct_1(X0) | k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f32])).
% 1.38/0.57  fof(f32,plain,(
% 1.38/0.57    ! [X0] : ((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 1.38/0.57    inference(flattening,[],[f31])).
% 1.38/0.57  fof(f31,plain,(
% 1.38/0.57    ! [X0] : (((k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 1.38/0.57    inference(ennf_transformation,[],[f5])).
% 1.38/0.57  fof(f5,axiom,(
% 1.38/0.57    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k1_relat_1(X0) = k2_relat_1(k2_funct_1(X0)) & k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)))))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_funct_1)).
% 1.38/0.57  fof(f151,plain,(
% 1.38/0.57    spl3_3),
% 1.38/0.57    inference(avatar_contradiction_clause,[],[f149])).
% 1.38/0.57  fof(f149,plain,(
% 1.38/0.57    $false | spl3_3),
% 1.38/0.57    inference(resolution,[],[f144,f114])).
% 1.38/0.57  fof(f144,plain,(
% 1.38/0.57    ( ! [X0,X1] : (~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) ) | spl3_3),
% 1.38/0.57    inference(resolution,[],[f134,f84])).
% 1.38/0.57  fof(f84,plain,(
% 1.38/0.57    ( ! [X2,X0,X1] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))) )),
% 1.38/0.57    inference(cnf_transformation,[],[f39])).
% 1.38/0.57  fof(f39,plain,(
% 1.38/0.57    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 1.38/0.57    inference(ennf_transformation,[],[f7])).
% 1.38/0.57  fof(f7,axiom,(
% 1.38/0.57    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',cc1_relset_1)).
% 1.38/0.57  fof(f134,plain,(
% 1.38/0.57    ~v1_relat_1(sK2) | spl3_3),
% 1.38/0.57    inference(avatar_component_clause,[],[f132])).
% 1.38/0.57  fof(f146,plain,(
% 1.38/0.57    spl3_4),
% 1.38/0.57    inference(avatar_contradiction_clause,[],[f145])).
% 1.38/0.57  fof(f145,plain,(
% 1.38/0.57    $false | spl3_4),
% 1.38/0.57    inference(resolution,[],[f138,f60])).
% 1.38/0.57  fof(f60,plain,(
% 1.38/0.57    v1_funct_1(sK2)),
% 1.38/0.57    inference(cnf_transformation,[],[f55])).
% 1.38/0.57  fof(f138,plain,(
% 1.38/0.57    ~v1_funct_1(sK2) | spl3_4),
% 1.38/0.57    inference(avatar_component_clause,[],[f136])).
% 1.38/0.57  fof(f143,plain,(
% 1.38/0.57    ~spl3_3 | ~spl3_4 | spl3_5),
% 1.38/0.57    inference(avatar_split_clause,[],[f129,f140,f136,f132])).
% 1.38/0.57  fof(f129,plain,(
% 1.38/0.57    k2_relat_1(sK2) = k1_relat_1(k2_funct_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2)),
% 1.38/0.57    inference(resolution,[],[f77,f64])).
% 1.38/0.57  fof(f77,plain,(
% 1.38/0.57    ( ! [X0] : (~v2_funct_1(X0) | k2_relat_1(X0) = k1_relat_1(k2_funct_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 1.38/0.57    inference(cnf_transformation,[],[f32])).
% 1.38/0.57  fof(f128,plain,(
% 1.38/0.57    spl3_1),
% 1.38/0.57    inference(avatar_contradiction_clause,[],[f127])).
% 1.38/0.57  fof(f127,plain,(
% 1.38/0.57    $false | spl3_1),
% 1.38/0.57    inference(resolution,[],[f121,f59])).
% 1.38/0.57  fof(f121,plain,(
% 1.38/0.57    ~l1_struct_0(sK1) | spl3_1),
% 1.38/0.57    inference(avatar_component_clause,[],[f119])).
% 1.38/0.57  fof(f119,plain,(
% 1.38/0.57    spl3_1 <=> l1_struct_0(sK1)),
% 1.38/0.57    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 1.38/0.57  fof(f126,plain,(
% 1.38/0.57    ~spl3_1 | ~spl3_2),
% 1.38/0.57    inference(avatar_split_clause,[],[f117,f123,f119])).
% 1.38/0.57  fof(f117,plain,(
% 1.38/0.57    ~v1_xboole_0(k2_struct_0(sK1)) | ~l1_struct_0(sK1)),
% 1.38/0.57    inference(forward_demodulation,[],[f116,f107])).
% 1.38/0.57  fof(f116,plain,(
% 1.38/0.57    ~l1_struct_0(sK1) | ~v1_xboole_0(u1_struct_0(sK1))),
% 1.38/0.57    inference(resolution,[],[f71,f58])).
% 1.38/0.57  fof(f58,plain,(
% 1.38/0.57    ~v2_struct_0(sK1)),
% 1.38/0.57    inference(cnf_transformation,[],[f55])).
% 1.38/0.57  fof(f71,plain,(
% 1.38/0.57    ( ! [X0] : (v2_struct_0(X0) | ~l1_struct_0(X0) | ~v1_xboole_0(u1_struct_0(X0))) )),
% 1.38/0.57    inference(cnf_transformation,[],[f26])).
% 1.38/0.57  fof(f26,plain,(
% 1.38/0.57    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | ~l1_struct_0(X0) | v2_struct_0(X0))),
% 1.38/0.57    inference(flattening,[],[f25])).
% 1.38/0.57  fof(f25,plain,(
% 1.38/0.57    ! [X0] : (~v1_xboole_0(u1_struct_0(X0)) | (~l1_struct_0(X0) | v2_struct_0(X0)))),
% 1.38/0.57    inference(ennf_transformation,[],[f18])).
% 1.38/0.57  fof(f18,axiom,(
% 1.38/0.57    ! [X0] : ((l1_struct_0(X0) & ~v2_struct_0(X0)) => ~v1_xboole_0(u1_struct_0(X0)))),
% 1.38/0.57    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc2_struct_0)).
% 1.38/0.57  % SZS output end Proof for theBenchmark
% 1.38/0.57  % (24124)------------------------------
% 1.38/0.57  % (24124)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 1.38/0.57  % (24124)Termination reason: Refutation
% 1.38/0.57  
% 1.38/0.57  % (24124)Memory used [KB]: 6524
% 1.38/0.57  % (24124)Time elapsed: 0.149 s
% 1.38/0.57  % (24124)------------------------------
% 1.38/0.57  % (24124)------------------------------
% 1.38/0.57  % (24111)Success in time 0.206 s
%------------------------------------------------------------------------------
