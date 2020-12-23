%------------------------------------------------------------------------------
% File       : Vampire---4.5
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : run_vampire %s %d

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 13:14:35 EST 2020

% Result     : Theorem 0.21s
% Output     : Refutation 0.21s
% Verified   : 
% Statistics : Number of formulae       :  153 ( 312 expanded)
%              Number of leaves         :   46 ( 154 expanded)
%              Depth                    :    9
%              Number of atoms          :  546 (1448 expanded)
%              Number of equality atoms :  144 ( 429 expanded)
%              Maximal formula depth    :   12 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
fof(f367,plain,(
    $false ),
    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f85,f90,f95,f106,f111,f117,f123,f130,f137,f150,f155,f156,f163,f176,f181,f222,f224,f254,f255,f276,f284,f346,f347,f360,f366])).

fof(f366,plain,
    ( k1_relat_1(sK2) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | u1_struct_0(sK0) != k2_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k6_relat_1(k1_relat_1(sK2)) != k1_partfun1(k2_struct_0(sK0),k2_relat_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0),sK2,k2_funct_1(sK2))
    | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = k6_relat_1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f360,plain,
    ( ~ spl3_7
    | spl3_47
    | ~ spl3_11
    | ~ spl3_27
    | ~ spl3_35 ),
    inference(avatar_split_clause,[],[f355,f282,f208,f103,f357,f82])).

fof(f82,plain,
    ( spl3_7
  <=> v1_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).

fof(f357,plain,
    ( spl3_47
  <=> k6_relat_1(k1_relat_1(sK2)) = k1_partfun1(k2_struct_0(sK0),k2_relat_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).

fof(f103,plain,
    ( spl3_11
  <=> k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).

fof(f208,plain,
    ( spl3_27
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).

fof(f282,plain,
    ( spl3_35
  <=> ! [X1,X0,X2] :
        ( k1_partfun1(X0,X1,k2_relat_1(sK2),k2_struct_0(sK0),X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).

fof(f355,plain,
    ( k6_relat_1(k1_relat_1(sK2)) = k1_partfun1(k2_struct_0(sK0),k2_relat_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0),sK2,k2_funct_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_11
    | ~ spl3_27
    | ~ spl3_35 ),
    inference(forward_demodulation,[],[f353,f105])).

fof(f105,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ spl3_11 ),
    inference(avatar_component_clause,[],[f103])).

fof(f353,plain,
    ( ~ v1_funct_1(sK2)
    | k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(k2_struct_0(sK0),k2_relat_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0),sK2,k2_funct_1(sK2))
    | ~ spl3_27
    | ~ spl3_35 ),
    inference(resolution,[],[f283,f209])).

fof(f209,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ spl3_27 ),
    inference(avatar_component_clause,[],[f208])).

fof(f283,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | k1_partfun1(X0,X1,k2_relat_1(sK2),k2_struct_0(sK0),X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2)) )
    | ~ spl3_35 ),
    inference(avatar_component_clause,[],[f282])).

fof(f347,plain,
    ( k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | u1_struct_0(sK0) != k2_struct_0(sK0)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | k6_relat_1(k2_relat_1(sK2)) != k1_partfun1(k2_relat_1(sK2),k2_struct_0(sK0),k2_struct_0(sK0),k2_relat_1(sK2),k2_funct_1(sK2),sK2)
    | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) = k6_relat_1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f346,plain,
    ( ~ spl3_22
    | spl3_46
    | ~ spl3_12
    | ~ spl3_29
    | ~ spl3_33 ),
    inference(avatar_split_clause,[],[f341,f252,f218,f108,f343,f178])).

fof(f178,plain,
    ( spl3_22
  <=> v1_funct_1(k2_funct_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).

fof(f343,plain,
    ( spl3_46
  <=> k6_relat_1(k2_relat_1(sK2)) = k1_partfun1(k2_relat_1(sK2),k2_struct_0(sK0),k2_struct_0(sK0),k2_relat_1(sK2),k2_funct_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).

fof(f108,plain,
    ( spl3_12
  <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).

fof(f218,plain,
    ( spl3_29
  <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).

fof(f252,plain,
    ( spl3_33
  <=> ! [X1,X0,X2] :
        ( k5_relat_1(X2,sK2) = k1_partfun1(X0,X1,k2_struct_0(sK0),k2_relat_1(sK2),X2,sK2)
        | ~ v1_funct_1(X2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).

fof(f341,plain,
    ( k6_relat_1(k2_relat_1(sK2)) = k1_partfun1(k2_relat_1(sK2),k2_struct_0(sK0),k2_struct_0(sK0),k2_relat_1(sK2),k2_funct_1(sK2),sK2)
    | ~ v1_funct_1(k2_funct_1(sK2))
    | ~ spl3_12
    | ~ spl3_29
    | ~ spl3_33 ),
    inference(forward_demodulation,[],[f335,f110])).

fof(f110,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ spl3_12 ),
    inference(avatar_component_clause,[],[f108])).

fof(f335,plain,
    ( ~ v1_funct_1(k2_funct_1(sK2))
    | k5_relat_1(k2_funct_1(sK2),sK2) = k1_partfun1(k2_relat_1(sK2),k2_struct_0(sK0),k2_struct_0(sK0),k2_relat_1(sK2),k2_funct_1(sK2),sK2)
    | ~ spl3_29
    | ~ spl3_33 ),
    inference(resolution,[],[f253,f220])).

fof(f220,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ spl3_29 ),
    inference(avatar_component_clause,[],[f218])).

fof(f253,plain,
    ( ! [X2,X0,X1] :
        ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2)
        | k5_relat_1(X2,sK2) = k1_partfun1(X0,X1,k2_struct_0(sK0),k2_relat_1(sK2),X2,sK2) )
    | ~ spl3_33 ),
    inference(avatar_component_clause,[],[f252])).

fof(f284,plain,
    ( ~ spl3_22
    | spl3_35
    | ~ spl3_29 ),
    inference(avatar_split_clause,[],[f277,f218,f282,f178])).

fof(f277,plain,
    ( ! [X2,X0,X1] :
        ( k1_partfun1(X0,X1,k2_relat_1(sK2),k2_struct_0(sK0),X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))
        | ~ v1_funct_1(k2_funct_1(sK2))
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl3_29 ),
    inference(resolution,[],[f220,f49])).

fof(f49,plain,(
    ! [X4,X2,X0,X5,X3,X1] :
      ( ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(cnf_transformation,[],[f25])).

fof(f25,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(flattening,[],[f24])).

fof(f24,plain,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5)
      | ~ m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
      | ~ v1_funct_1(X5)
      | ~ m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_1(X4) ) ),
    inference(ennf_transformation,[],[f5])).

fof(f5,axiom,(
    ! [X0,X1,X2,X3,X4,X5] :
      ( ( m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3)))
        & v1_funct_1(X5)
        & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        & v1_funct_1(X4) )
     => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).

fof(f276,plain,
    ( ~ spl3_7
    | ~ spl3_26
    | ~ spl3_27
    | ~ spl3_3
    | spl3_29
    | ~ spl3_30 ),
    inference(avatar_split_clause,[],[f271,f231,f218,f62,f208,f204,f82])).

fof(f204,plain,
    ( spl3_26
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).

fof(f62,plain,
    ( spl3_3
  <=> v2_funct_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).

fof(f231,plain,
    ( spl3_30
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).

fof(f271,plain,
    ( m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_30 ),
    inference(trivial_inequality_removal,[],[f270])).

fof(f270,plain,
    ( k2_relat_1(sK2) != k2_relat_1(sK2)
    | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ spl3_30 ),
    inference(superposition,[],[f47,f233])).

fof(f233,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_30 ),
    inference(avatar_component_clause,[],[f231])).

fof(f47,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f21,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f20])).

fof(f20,plain,(
    ! [X0,X1,X2] :
      ( ( m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0)))
        & v1_funct_2(k2_funct_1(X2),X1,X0)
        & v1_funct_1(k2_funct_1(X2)) )
      | k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(ennf_transformation,[],[f7])).

fof(f7,axiom,(
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

fof(f255,plain,
    ( spl3_30
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f248,f208,f231])).

fof(f248,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)
    | ~ spl3_27 ),
    inference(resolution,[],[f209,f44])).

fof(f44,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f19])).

fof(f19,plain,(
    ! [X0,X1,X2] :
      ( k2_relset_1(X0,X1,X2) = k2_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f4])).

fof(f4,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k2_relset_1(X0,X1,X2) = k2_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).

fof(f254,plain,
    ( ~ spl3_7
    | spl3_33
    | ~ spl3_27 ),
    inference(avatar_split_clause,[],[f247,f208,f252,f82])).

fof(f247,plain,
    ( ! [X2,X0,X1] :
        ( k5_relat_1(X2,sK2) = k1_partfun1(X0,X1,k2_struct_0(sK0),k2_relat_1(sK2),X2,sK2)
        | ~ v1_funct_1(sK2)
        | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
        | ~ v1_funct_1(X2) )
    | ~ spl3_27 ),
    inference(resolution,[],[f209,f49])).

fof(f224,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f222,plain,
    ( u1_struct_0(sK0) != k2_struct_0(sK0)
    | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | u1_struct_0(sK1) != k2_struct_0(sK1)
    | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))
    | ~ v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(theory_tautology_sat_conflict,[])).

fof(f181,plain,
    ( ~ spl3_7
    | ~ spl3_15
    | ~ spl3_16
    | ~ spl3_3
    | spl3_22
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f170,f160,f178,f62,f134,f127,f82])).

fof(f127,plain,
    ( spl3_15
  <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).

fof(f134,plain,
    ( spl3_16
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).

fof(f160,plain,
    ( spl3_20
  <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).

fof(f170,plain,
    ( v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl3_20 ),
    inference(trivial_inequality_removal,[],[f165])).

fof(f165,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | v1_funct_1(k2_funct_1(sK2))
    | ~ v2_funct_1(sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl3_20 ),
    inference(superposition,[],[f45,f162])).

fof(f162,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_20 ),
    inference(avatar_component_clause,[],[f160])).

fof(f45,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | v1_funct_1(k2_funct_1(X2))
      | ~ v2_funct_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f21])).

fof(f176,plain,
    ( ~ spl3_7
    | ~ spl3_15
    | ~ spl3_16
    | spl3_21
    | ~ spl3_3
    | ~ spl3_20 ),
    inference(avatar_split_clause,[],[f171,f160,f62,f173,f134,f127,f82])).

fof(f173,plain,
    ( spl3_21
  <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).

fof(f171,plain,
    ( ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl3_20 ),
    inference(trivial_inequality_removal,[],[f164])).

fof(f164,plain,
    ( k2_struct_0(sK1) != k2_struct_0(sK1)
    | ~ v2_funct_1(sK2)
    | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ v1_funct_1(sK2)
    | ~ spl3_20 ),
    inference(superposition,[],[f48,f162])).

fof(f48,plain,(
    ! [X2,X0,X1] :
      ( k2_relset_1(X0,X1,X2) != X1
      | ~ v2_funct_1(X2)
      | k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(cnf_transformation,[],[f23])).

fof(f23,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
      | ~ v2_funct_1(X2)
      | k2_relset_1(X0,X1,X2) != X1
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | ~ v1_funct_2(X2,X0,X1)
      | ~ v1_funct_1(X2) ) ),
    inference(flattening,[],[f22])).

fof(f22,plain,(
    ! [X0,X1,X2] :
      ( k2_funct_1(X2) = k2_tops_2(X0,X1,X2)
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
       => k2_funct_1(X2) = k2_tops_2(X0,X1,X2) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).

fof(f163,plain,
    ( spl3_20
    | ~ spl3_4
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f158,f120,f114,f67,f160])).

fof(f67,plain,
    ( spl3_4
  <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).

fof(f114,plain,
    ( spl3_13
  <=> u1_struct_0(sK1) = k2_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).

fof(f120,plain,
    ( spl3_14
  <=> u1_struct_0(sK0) = k2_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).

fof(f158,plain,
    ( k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f157,f122])).

fof(f122,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_14 ),
    inference(avatar_component_clause,[],[f120])).

fof(f157,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_4
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f69,f116])).

fof(f116,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_13 ),
    inference(avatar_component_clause,[],[f114])).

fof(f69,plain,
    ( k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    | ~ spl3_4 ),
    inference(avatar_component_clause,[],[f67])).

fof(f156,plain,
    ( spl3_10
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f141,f134,f99])).

fof(f99,plain,
    ( spl3_10
  <=> v1_relat_1(sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).

fof(f141,plain,
    ( v1_relat_1(sK2)
    | ~ spl3_16 ),
    inference(resolution,[],[f136,f42])).

fof(f42,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | v1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f17])).

fof(f17,plain,(
    ! [X0,X1,X2] :
      ( v1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f2])).

fof(f2,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => v1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).

fof(f136,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_16 ),
    inference(avatar_component_clause,[],[f134])).

fof(f155,plain,
    ( spl3_19
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f140,f134,f152])).

fof(f152,plain,
    ( spl3_19
  <=> k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).

fof(f140,plain,
    ( k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_16 ),
    inference(resolution,[],[f136,f43])).

fof(f43,plain,(
    ! [X2,X0,X1] :
      ( ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
      | k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    inference(cnf_transformation,[],[f18])).

fof(f18,plain,(
    ! [X0,X1,X2] :
      ( k1_relset_1(X0,X1,X2) = k1_relat_1(X2)
      | ~ m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) ) ),
    inference(ennf_transformation,[],[f3])).

fof(f3,axiom,(
    ! [X0,X1,X2] :
      ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1)))
     => k1_relset_1(X0,X1,X2) = k1_relat_1(X2) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).

fof(f150,plain,
    ( spl3_18
    | ~ spl3_16 ),
    inference(avatar_split_clause,[],[f139,f134,f147])).

fof(f147,plain,
    ( spl3_18
  <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).

fof(f139,plain,
    ( k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)
    | ~ spl3_16 ),
    inference(resolution,[],[f136,f44])).

fof(f137,plain,
    ( spl3_16
    | ~ spl3_5
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f132,f120,f114,f72,f134])).

fof(f72,plain,
    ( spl3_5
  <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).

fof(f132,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_5
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f131,f122])).

fof(f131,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1))))
    | ~ spl3_5
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f74,f116])).

fof(f74,plain,
    ( m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    | ~ spl3_5 ),
    inference(avatar_component_clause,[],[f72])).

fof(f130,plain,
    ( spl3_15
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(avatar_split_clause,[],[f125,f120,f114,f77,f127])).

fof(f77,plain,
    ( spl3_6
  <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).

fof(f125,plain,
    ( v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_13
    | ~ spl3_14 ),
    inference(forward_demodulation,[],[f124,f122])).

fof(f124,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1))
    | ~ spl3_6
    | ~ spl3_13 ),
    inference(forward_demodulation,[],[f79,f116])).

fof(f79,plain,
    ( v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    | ~ spl3_6 ),
    inference(avatar_component_clause,[],[f77])).

fof(f123,plain,
    ( spl3_14
    | ~ spl3_9 ),
    inference(avatar_split_clause,[],[f118,f92,f120])).

fof(f92,plain,
    ( spl3_9
  <=> l1_struct_0(sK0) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).

fof(f118,plain,
    ( u1_struct_0(sK0) = k2_struct_0(sK0)
    | ~ spl3_9 ),
    inference(resolution,[],[f94,f39])).

fof(f39,plain,(
    ! [X0] :
      ( ~ l1_struct_0(X0)
      | k2_struct_0(X0) = u1_struct_0(X0) ) ),
    inference(cnf_transformation,[],[f14])).

fof(f14,plain,(
    ! [X0] :
      ( k2_struct_0(X0) = u1_struct_0(X0)
      | ~ l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f8])).

fof(f8,axiom,(
    ! [X0] :
      ( l1_struct_0(X0)
     => k2_struct_0(X0) = u1_struct_0(X0) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).

fof(f94,plain,
    ( l1_struct_0(sK0)
    | ~ spl3_9 ),
    inference(avatar_component_clause,[],[f92])).

fof(f117,plain,
    ( spl3_13
    | ~ spl3_8 ),
    inference(avatar_split_clause,[],[f112,f87,f114])).

fof(f87,plain,
    ( spl3_8
  <=> l1_struct_0(sK1) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).

fof(f112,plain,
    ( u1_struct_0(sK1) = k2_struct_0(sK1)
    | ~ spl3_8 ),
    inference(resolution,[],[f89,f39])).

fof(f89,plain,
    ( l1_struct_0(sK1)
    | ~ spl3_8 ),
    inference(avatar_component_clause,[],[f87])).

fof(f111,plain,
    ( ~ spl3_10
    | ~ spl3_7
    | spl3_12
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f97,f62,f108,f82,f99])).

fof(f97,plain,
    ( k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f64,f41])).

fof(f41,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f16,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(flattening,[],[f15])).

fof(f15,plain,(
    ! [X0] :
      ( ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
        & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) )
      | ~ v2_funct_1(X0)
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(ennf_transformation,[],[f1])).

fof(f1,axiom,(
    ! [X0] :
      ( ( v1_funct_1(X0)
        & v1_relat_1(X0) )
     => ( v2_funct_1(X0)
       => ( k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0))
          & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).

fof(f64,plain,
    ( v2_funct_1(sK2)
    | ~ spl3_3 ),
    inference(avatar_component_clause,[],[f62])).

fof(f106,plain,
    ( ~ spl3_10
    | ~ spl3_7
    | spl3_11
    | ~ spl3_3 ),
    inference(avatar_split_clause,[],[f96,f62,f103,f82,f99])).

fof(f96,plain,
    ( k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))
    | ~ v1_funct_1(sK2)
    | ~ v1_relat_1(sK2)
    | ~ spl3_3 ),
    inference(resolution,[],[f64,f40])).

fof(f40,plain,(
    ! [X0] :
      ( ~ v2_funct_1(X0)
      | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))
      | ~ v1_funct_1(X0)
      | ~ v1_relat_1(X0) ) ),
    inference(cnf_transformation,[],[f16])).

fof(f95,plain,(
    spl3_9 ),
    inference(avatar_split_clause,[],[f30,f92])).

fof(f30,plain,(
    l1_struct_0(sK0) ),
    inference(cnf_transformation,[],[f29])).

fof(f29,plain,
    ( ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
      | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) )
    & v2_funct_1(sK2)
    & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
    & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
    & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
    & v1_funct_1(sK2)
    & l1_struct_0(sK1)
    & l1_struct_0(sK0) ),
    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f28,f27,f26])).

fof(f26,plain,
    ( ? [X0] :
        ( ? [X1] :
            ( ? [X2] :
                ( ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))
                  | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) )
                & v2_funct_1(X2)
                & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
                & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                & v1_funct_1(X2) )
            & l1_struct_0(X1) )
        & l1_struct_0(X0) )
   => ( ? [X1] :
          ( ? [X2] :
              ( ( k1_partfun1(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2))
                | k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(sK0) ) ),
    introduced(choice_axiom,[])).

fof(f27,plain,
    ( ? [X1] :
        ( ? [X2] :
            ( ( k1_partfun1(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2))
              | k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)) )
            & v2_funct_1(X2)
            & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)
            & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1))))
            & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1))
            & v1_funct_1(X2) )
        & l1_struct_0(X1) )
   => ( ? [X2] :
          ( ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2))
            | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),X2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)) )
          & v2_funct_1(X2)
          & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
          & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
          & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
          & v1_funct_1(X2) )
      & l1_struct_0(sK1) ) ),
    introduced(choice_axiom,[])).

fof(f28,plain,
    ( ? [X2] :
        ( ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2))
          | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),X2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)) )
        & v2_funct_1(X2)
        & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1)
        & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
        & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1))
        & v1_funct_1(X2) )
   => ( ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
        | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) )
      & v2_funct_1(sK2)
      & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)
      & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))
      & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))
      & v1_funct_1(sK2) ) ),
    introduced(choice_axiom,[])).

fof(f13,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(flattening,[],[f12])).

fof(f12,plain,(
    ? [X0] :
      ( ? [X1] :
          ( ? [X2] :
              ( ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))
                | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) )
              & v2_funct_1(X2)
              & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)
              & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
              & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
              & v1_funct_1(X2) )
          & l1_struct_0(X1) )
      & l1_struct_0(X0) ) ),
    inference(ennf_transformation,[],[f11])).

fof(f11,negated_conjecture,(
    ~ ! [X0] :
        ( l1_struct_0(X0)
       => ! [X1] :
            ( l1_struct_0(X1)
           => ! [X2] :
                ( ( m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1))))
                  & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1))
                  & v1_funct_1(X2) )
               => ( ( v2_funct_1(X2)
                    & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) )
                 => ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) = k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))
                    & k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    inference(negated_conjecture,[],[f10])).

fof(f10,conjecture,(
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
               => ( k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) = k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))
                  & k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) ) ) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_2)).

fof(f90,plain,(
    spl3_8 ),
    inference(avatar_split_clause,[],[f31,f87])).

fof(f31,plain,(
    l1_struct_0(sK1) ),
    inference(cnf_transformation,[],[f29])).

fof(f85,plain,(
    spl3_7 ),
    inference(avatar_split_clause,[],[f32,f82])).

fof(f32,plain,(
    v1_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f80,plain,(
    spl3_6 ),
    inference(avatar_split_clause,[],[f33,f77])).

fof(f33,plain,(
    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) ),
    inference(cnf_transformation,[],[f29])).

fof(f75,plain,(
    spl3_5 ),
    inference(avatar_split_clause,[],[f34,f72])).

fof(f34,plain,(
    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) ),
    inference(cnf_transformation,[],[f29])).

fof(f70,plain,(
    spl3_4 ),
    inference(avatar_split_clause,[],[f35,f67])).

fof(f35,plain,(
    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f65,plain,(
    spl3_3 ),
    inference(avatar_split_clause,[],[f36,f62])).

fof(f36,plain,(
    v2_funct_1(sK2) ),
    inference(cnf_transformation,[],[f29])).

fof(f60,plain,
    ( ~ spl3_1
    | ~ spl3_2 ),
    inference(avatar_split_clause,[],[f51,f57,f53])).

fof(f53,plain,
    ( spl3_1
  <=> k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) = k6_relat_1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).

fof(f57,plain,
    ( spl3_2
  <=> k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = k6_relat_1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).

fof(f51,plain,
    ( k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_relat_1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f50,f38])).

fof(f38,plain,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    inference(cnf_transformation,[],[f6])).

fof(f6,axiom,(
    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).

fof(f50,plain,
    ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_relat_1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(forward_demodulation,[],[f37,f38])).

fof(f37,plain,
    ( k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))
    | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) ),
    inference(cnf_transformation,[],[f29])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : run_vampire %s %d
% 0.14/0.35  % Computer   : n018.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % WCLimit    : 600
% 0.14/0.35  % DateTime   : Tue Dec  1 17:56:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.21/0.43  % (16205)dis+10_128_acc=on:add=off:afp=4000:afq=1.4:amm=off:bd=preordered:bce=on:cond=on:fsr=off:fde=unused:gs=on:gsem=on:irw=on:lma=on:nm=64:nwc=1.2:nicw=on:sos=on:sp=occurrence:updr=off:uhcvi=on_122 on theBenchmark
% 0.21/0.44  % (16205)Refutation found. Thanks to Tanya!
% 0.21/0.44  % SZS status Theorem for theBenchmark
% 0.21/0.44  % SZS output start Proof for theBenchmark
% 0.21/0.44  fof(f367,plain,(
% 0.21/0.44    $false),
% 0.21/0.44    inference(avatar_sat_refutation,[],[f60,f65,f70,f75,f80,f85,f90,f95,f106,f111,f117,f123,f130,f137,f150,f155,f156,f163,f176,f181,f222,f224,f254,f255,f276,f284,f346,f347,f360,f366])).
% 0.21/0.44  fof(f366,plain,(
% 0.21/0.44    k1_relat_1(sK2) != k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | u1_struct_0(sK0) != k2_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k6_relat_1(k1_relat_1(sK2)) != k1_partfun1(k2_struct_0(sK0),k2_relat_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = k6_relat_1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.44  fof(f360,plain,(
% 0.21/0.44    ~spl3_7 | spl3_47 | ~spl3_11 | ~spl3_27 | ~spl3_35),
% 0.21/0.44    inference(avatar_split_clause,[],[f355,f282,f208,f103,f357,f82])).
% 0.21/0.44  fof(f82,plain,(
% 0.21/0.44    spl3_7 <=> v1_funct_1(sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_7])])).
% 0.21/0.44  fof(f357,plain,(
% 0.21/0.44    spl3_47 <=> k6_relat_1(k1_relat_1(sK2)) = k1_partfun1(k2_struct_0(sK0),k2_relat_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0),sK2,k2_funct_1(sK2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_47])])).
% 0.21/0.44  fof(f103,plain,(
% 0.21/0.44    spl3_11 <=> k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_11])])).
% 0.21/0.44  fof(f208,plain,(
% 0.21/0.44    spl3_27 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_27])])).
% 0.21/0.44  fof(f282,plain,(
% 0.21/0.44    spl3_35 <=> ! [X1,X0,X2] : (k1_partfun1(X0,X1,k2_relat_1(sK2),k2_struct_0(sK0),X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2)) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_35])])).
% 0.21/0.44  fof(f355,plain,(
% 0.21/0.44    k6_relat_1(k1_relat_1(sK2)) = k1_partfun1(k2_struct_0(sK0),k2_relat_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) | ~v1_funct_1(sK2) | (~spl3_11 | ~spl3_27 | ~spl3_35)),
% 0.21/0.44    inference(forward_demodulation,[],[f353,f105])).
% 0.21/0.44  fof(f105,plain,(
% 0.21/0.44    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | ~spl3_11),
% 0.21/0.44    inference(avatar_component_clause,[],[f103])).
% 0.21/0.44  fof(f353,plain,(
% 0.21/0.44    ~v1_funct_1(sK2) | k5_relat_1(sK2,k2_funct_1(sK2)) = k1_partfun1(k2_struct_0(sK0),k2_relat_1(sK2),k2_relat_1(sK2),k2_struct_0(sK0),sK2,k2_funct_1(sK2)) | (~spl3_27 | ~spl3_35)),
% 0.21/0.44    inference(resolution,[],[f283,f209])).
% 0.21/0.44  fof(f209,plain,(
% 0.21/0.44    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~spl3_27),
% 0.21/0.44    inference(avatar_component_clause,[],[f208])).
% 0.21/0.44  fof(f283,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k1_partfun1(X0,X1,k2_relat_1(sK2),k2_struct_0(sK0),X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2))) ) | ~spl3_35),
% 0.21/0.44    inference(avatar_component_clause,[],[f282])).
% 0.21/0.44  fof(f347,plain,(
% 0.21/0.44    k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | u1_struct_0(sK0) != k2_struct_0(sK0) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_funct_1(sK2) != k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | k6_relat_1(k2_relat_1(sK2)) != k1_partfun1(k2_relat_1(sK2),k2_struct_0(sK0),k2_struct_0(sK0),k2_relat_1(sK2),k2_funct_1(sK2),sK2) | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) = k6_relat_1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.44  fof(f346,plain,(
% 0.21/0.44    ~spl3_22 | spl3_46 | ~spl3_12 | ~spl3_29 | ~spl3_33),
% 0.21/0.44    inference(avatar_split_clause,[],[f341,f252,f218,f108,f343,f178])).
% 0.21/0.44  fof(f178,plain,(
% 0.21/0.44    spl3_22 <=> v1_funct_1(k2_funct_1(sK2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_22])])).
% 0.21/0.44  fof(f343,plain,(
% 0.21/0.44    spl3_46 <=> k6_relat_1(k2_relat_1(sK2)) = k1_partfun1(k2_relat_1(sK2),k2_struct_0(sK0),k2_struct_0(sK0),k2_relat_1(sK2),k2_funct_1(sK2),sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_46])])).
% 0.21/0.44  fof(f108,plain,(
% 0.21/0.44    spl3_12 <=> k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_12])])).
% 0.21/0.44  fof(f218,plain,(
% 0.21/0.44    spl3_29 <=> m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_29])])).
% 0.21/0.44  fof(f252,plain,(
% 0.21/0.44    spl3_33 <=> ! [X1,X0,X2] : (k5_relat_1(X2,sK2) = k1_partfun1(X0,X1,k2_struct_0(sK0),k2_relat_1(sK2),X2,sK2) | ~v1_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_33])])).
% 0.21/0.44  fof(f341,plain,(
% 0.21/0.44    k6_relat_1(k2_relat_1(sK2)) = k1_partfun1(k2_relat_1(sK2),k2_struct_0(sK0),k2_struct_0(sK0),k2_relat_1(sK2),k2_funct_1(sK2),sK2) | ~v1_funct_1(k2_funct_1(sK2)) | (~spl3_12 | ~spl3_29 | ~spl3_33)),
% 0.21/0.44    inference(forward_demodulation,[],[f335,f110])).
% 0.21/0.44  fof(f110,plain,(
% 0.21/0.44    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~spl3_12),
% 0.21/0.44    inference(avatar_component_clause,[],[f108])).
% 0.21/0.44  fof(f335,plain,(
% 0.21/0.44    ~v1_funct_1(k2_funct_1(sK2)) | k5_relat_1(k2_funct_1(sK2),sK2) = k1_partfun1(k2_relat_1(sK2),k2_struct_0(sK0),k2_struct_0(sK0),k2_relat_1(sK2),k2_funct_1(sK2),sK2) | (~spl3_29 | ~spl3_33)),
% 0.21/0.44    inference(resolution,[],[f253,f220])).
% 0.21/0.44  fof(f220,plain,(
% 0.21/0.44    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~spl3_29),
% 0.21/0.44    inference(avatar_component_clause,[],[f218])).
% 0.21/0.44  fof(f253,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2) | k5_relat_1(X2,sK2) = k1_partfun1(X0,X1,k2_struct_0(sK0),k2_relat_1(sK2),X2,sK2)) ) | ~spl3_33),
% 0.21/0.44    inference(avatar_component_clause,[],[f252])).
% 0.21/0.44  fof(f284,plain,(
% 0.21/0.44    ~spl3_22 | spl3_35 | ~spl3_29),
% 0.21/0.44    inference(avatar_split_clause,[],[f277,f218,f282,f178])).
% 0.21/0.44  fof(f277,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k1_partfun1(X0,X1,k2_relat_1(sK2),k2_struct_0(sK0),X2,k2_funct_1(sK2)) = k5_relat_1(X2,k2_funct_1(sK2)) | ~v1_funct_1(k2_funct_1(sK2)) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | ~spl3_29),
% 0.21/0.44    inference(resolution,[],[f220,f49])).
% 0.21/0.44  fof(f49,plain,(
% 0.21/0.44    ( ! [X4,X2,X0,X5,X3,X1] : (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f25])).
% 0.21/0.44  fof(f25,plain,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | ~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4))),
% 0.21/0.44    inference(flattening,[],[f24])).
% 0.21/0.44  fof(f24,plain,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4,X5] : (k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5) | (~m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) | ~v1_funct_1(X5) | ~m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X4)))),
% 0.21/0.44    inference(ennf_transformation,[],[f5])).
% 0.21/0.44  fof(f5,axiom,(
% 0.21/0.44    ! [X0,X1,X2,X3,X4,X5] : ((m1_subset_1(X5,k1_zfmisc_1(k2_zfmisc_1(X2,X3))) & v1_funct_1(X5) & m1_subset_1(X4,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_1(X4)) => k1_partfun1(X0,X1,X2,X3,X4,X5) = k5_relat_1(X4,X5))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_partfun1)).
% 0.21/0.44  fof(f276,plain,(
% 0.21/0.44    ~spl3_7 | ~spl3_26 | ~spl3_27 | ~spl3_3 | spl3_29 | ~spl3_30),
% 0.21/0.44    inference(avatar_split_clause,[],[f271,f231,f218,f62,f208,f204,f82])).
% 0.21/0.44  fof(f204,plain,(
% 0.21/0.44    spl3_26 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_26])])).
% 0.21/0.44  fof(f62,plain,(
% 0.21/0.44    spl3_3 <=> v2_funct_1(sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_3])])).
% 0.21/0.44  fof(f231,plain,(
% 0.21/0.44    spl3_30 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_30])])).
% 0.21/0.44  fof(f271,plain,(
% 0.21/0.44    m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~spl3_30),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f270])).
% 0.21/0.44  fof(f270,plain,(
% 0.21/0.44    k2_relat_1(sK2) != k2_relat_1(sK2) | m1_subset_1(k2_funct_1(sK2),k1_zfmisc_1(k2_zfmisc_1(k2_relat_1(sK2),k2_struct_0(sK0)))) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~spl3_30),
% 0.21/0.44    inference(superposition,[],[f47,f233])).
% 0.21/0.44  fof(f233,plain,(
% 0.21/0.44    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_30),
% 0.21/0.44    inference(avatar_component_clause,[],[f231])).
% 0.21/0.44  fof(f47,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f21])).
% 0.21/0.44  fof(f21,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.44    inference(flattening,[],[f20])).
% 0.21/0.44  fof(f20,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (((m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2))) | (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2))) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.44    inference(ennf_transformation,[],[f7])).
% 0.21/0.44  fof(f7,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((k2_relset_1(X0,X1,X2) = X1 & v2_funct_1(X2)) => (m1_subset_1(k2_funct_1(X2),k1_zfmisc_1(k2_zfmisc_1(X1,X0))) & v1_funct_2(k2_funct_1(X2),X1,X0) & v1_funct_1(k2_funct_1(X2)))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t31_funct_2)).
% 0.21/0.44  fof(f255,plain,(
% 0.21/0.44    spl3_30 | ~spl3_27),
% 0.21/0.44    inference(avatar_split_clause,[],[f248,f208,f231])).
% 0.21/0.44  fof(f248,plain,(
% 0.21/0.44    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_relat_1(sK2),sK2) | ~spl3_27),
% 0.21/0.44    inference(resolution,[],[f209,f44])).
% 0.21/0.44  fof(f44,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k2_relset_1(X0,X1,X2) = k2_relat_1(X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f19])).
% 0.21/0.44  fof(f19,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (k2_relset_1(X0,X1,X2) = k2_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    inference(ennf_transformation,[],[f4])).
% 0.21/0.44  fof(f4,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k2_relset_1(X0,X1,X2) = k2_relat_1(X2))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k2_relset_1)).
% 0.21/0.44  fof(f254,plain,(
% 0.21/0.44    ~spl3_7 | spl3_33 | ~spl3_27),
% 0.21/0.44    inference(avatar_split_clause,[],[f247,f208,f252,f82])).
% 0.21/0.44  fof(f247,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k5_relat_1(X2,sK2) = k1_partfun1(X0,X1,k2_struct_0(sK0),k2_relat_1(sK2),X2,sK2) | ~v1_funct_1(sK2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_1(X2)) ) | ~spl3_27),
% 0.21/0.44    inference(resolution,[],[f209,f49])).
% 0.21/0.44  fof(f224,plain,(
% 0.21/0.44    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_relat_1(sK2)))) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.44  fof(f222,plain,(
% 0.21/0.44    u1_struct_0(sK0) != k2_struct_0(sK0) | k2_relat_1(sK2) != k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | u1_struct_0(sK1) != k2_struct_0(sK1) | k2_struct_0(sK1) != k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | v1_funct_2(sK2,k2_struct_0(sK0),k2_relat_1(sK2)) | ~v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.44    introduced(theory_tautology_sat_conflict,[])).
% 0.21/0.44  fof(f181,plain,(
% 0.21/0.44    ~spl3_7 | ~spl3_15 | ~spl3_16 | ~spl3_3 | spl3_22 | ~spl3_20),
% 0.21/0.44    inference(avatar_split_clause,[],[f170,f160,f178,f62,f134,f127,f82])).
% 0.21/0.44  fof(f127,plain,(
% 0.21/0.44    spl3_15 <=> v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_15])])).
% 0.21/0.44  fof(f134,plain,(
% 0.21/0.44    spl3_16 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_16])])).
% 0.21/0.44  fof(f160,plain,(
% 0.21/0.44    spl3_20 <=> k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_20])])).
% 0.21/0.44  fof(f170,plain,(
% 0.21/0.44    v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~spl3_20),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f165])).
% 0.21/0.44  fof(f165,plain,(
% 0.21/0.44    k2_struct_0(sK1) != k2_struct_0(sK1) | v1_funct_1(k2_funct_1(sK2)) | ~v2_funct_1(sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~spl3_20),
% 0.21/0.44    inference(superposition,[],[f45,f162])).
% 0.21/0.44  fof(f162,plain,(
% 0.21/0.44    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_20),
% 0.21/0.44    inference(avatar_component_clause,[],[f160])).
% 0.21/0.44  fof(f45,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | v1_funct_1(k2_funct_1(X2)) | ~v2_funct_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f21])).
% 0.21/0.44  fof(f176,plain,(
% 0.21/0.44    ~spl3_7 | ~spl3_15 | ~spl3_16 | spl3_21 | ~spl3_3 | ~spl3_20),
% 0.21/0.44    inference(avatar_split_clause,[],[f171,f160,f62,f173,f134,f127,f82])).
% 0.21/0.44  fof(f173,plain,(
% 0.21/0.44    spl3_21 <=> k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_21])])).
% 0.21/0.44  fof(f171,plain,(
% 0.21/0.44    ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~spl3_20),
% 0.21/0.44    inference(trivial_inequality_removal,[],[f164])).
% 0.21/0.44  fof(f164,plain,(
% 0.21/0.44    k2_struct_0(sK1) != k2_struct_0(sK1) | ~v2_funct_1(sK2) | k2_funct_1(sK2) = k2_tops_2(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | ~v1_funct_1(sK2) | ~spl3_20),
% 0.21/0.44    inference(superposition,[],[f48,f162])).
% 0.21/0.44  fof(f48,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (k2_relset_1(X0,X1,X2) != X1 | ~v2_funct_1(X2) | k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f23])).
% 0.21/0.44  fof(f23,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | ~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1 | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2))),
% 0.21/0.44    inference(flattening,[],[f22])).
% 0.21/0.44  fof(f22,plain,(
% 0.21/0.44    ! [X0,X1,X2] : ((k2_funct_1(X2) = k2_tops_2(X0,X1,X2) | (~v2_funct_1(X2) | k2_relset_1(X0,X1,X2) != X1)) | (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | ~v1_funct_2(X2,X0,X1) | ~v1_funct_1(X2)))),
% 0.21/0.44    inference(ennf_transformation,[],[f9])).
% 0.21/0.44  fof(f9,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) & v1_funct_2(X2,X0,X1) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(X0,X1,X2) = X1) => k2_funct_1(X2) = k2_tops_2(X0,X1,X2)))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_tops_2)).
% 0.21/0.44  fof(f163,plain,(
% 0.21/0.44    spl3_20 | ~spl3_4 | ~spl3_13 | ~spl3_14),
% 0.21/0.44    inference(avatar_split_clause,[],[f158,f120,f114,f67,f160])).
% 0.21/0.44  fof(f67,plain,(
% 0.21/0.44    spl3_4 <=> k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_4])])).
% 0.21/0.44  fof(f114,plain,(
% 0.21/0.44    spl3_13 <=> u1_struct_0(sK1) = k2_struct_0(sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_13])])).
% 0.21/0.44  fof(f120,plain,(
% 0.21/0.44    spl3_14 <=> u1_struct_0(sK0) = k2_struct_0(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_14])])).
% 0.21/0.44  fof(f158,plain,(
% 0.21/0.44    k2_struct_0(sK1) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_13 | ~spl3_14)),
% 0.21/0.44    inference(forward_demodulation,[],[f157,f122])).
% 0.21/0.44  fof(f122,plain,(
% 0.21/0.44    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_14),
% 0.21/0.44    inference(avatar_component_clause,[],[f120])).
% 0.21/0.44  fof(f157,plain,(
% 0.21/0.44    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),k2_struct_0(sK1),sK2) | (~spl3_4 | ~spl3_13)),
% 0.21/0.44    inference(forward_demodulation,[],[f69,f116])).
% 0.21/0.44  fof(f116,plain,(
% 0.21/0.44    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_13),
% 0.21/0.44    inference(avatar_component_clause,[],[f114])).
% 0.21/0.44  fof(f69,plain,(
% 0.21/0.44    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) | ~spl3_4),
% 0.21/0.44    inference(avatar_component_clause,[],[f67])).
% 0.21/0.44  fof(f156,plain,(
% 0.21/0.44    spl3_10 | ~spl3_16),
% 0.21/0.44    inference(avatar_split_clause,[],[f141,f134,f99])).
% 0.21/0.44  fof(f99,plain,(
% 0.21/0.44    spl3_10 <=> v1_relat_1(sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_10])])).
% 0.21/0.44  fof(f141,plain,(
% 0.21/0.44    v1_relat_1(sK2) | ~spl3_16),
% 0.21/0.44    inference(resolution,[],[f136,f42])).
% 0.21/0.44  fof(f42,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | v1_relat_1(X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f17])).
% 0.21/0.44  fof(f17,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (v1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    inference(ennf_transformation,[],[f2])).
% 0.21/0.44  fof(f2,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => v1_relat_1(X2))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',cc1_relset_1)).
% 0.21/0.44  fof(f136,plain,(
% 0.21/0.44    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | ~spl3_16),
% 0.21/0.44    inference(avatar_component_clause,[],[f134])).
% 0.21/0.44  fof(f155,plain,(
% 0.21/0.44    spl3_19 | ~spl3_16),
% 0.21/0.44    inference(avatar_split_clause,[],[f140,f134,f152])).
% 0.21/0.44  fof(f152,plain,(
% 0.21/0.44    spl3_19 <=> k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_19])])).
% 0.21/0.44  fof(f140,plain,(
% 0.21/0.44    k1_relat_1(sK2) = k1_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_16),
% 0.21/0.44    inference(resolution,[],[f136,f43])).
% 0.21/0.44  fof(f43,plain,(
% 0.21/0.44    ( ! [X2,X0,X1] : (~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) | k1_relset_1(X0,X1,X2) = k1_relat_1(X2)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f18])).
% 0.21/0.44  fof(f18,plain,(
% 0.21/0.44    ! [X0,X1,X2] : (k1_relset_1(X0,X1,X2) = k1_relat_1(X2) | ~m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))))),
% 0.21/0.44    inference(ennf_transformation,[],[f3])).
% 0.21/0.44  fof(f3,axiom,(
% 0.21/0.44    ! [X0,X1,X2] : (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(X0,X1))) => k1_relset_1(X0,X1,X2) = k1_relat_1(X2))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k1_relset_1)).
% 0.21/0.44  fof(f150,plain,(
% 0.21/0.44    spl3_18 | ~spl3_16),
% 0.21/0.44    inference(avatar_split_clause,[],[f139,f134,f147])).
% 0.21/0.44  fof(f147,plain,(
% 0.21/0.44    spl3_18 <=> k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_18])])).
% 0.21/0.44  fof(f139,plain,(
% 0.21/0.44    k2_relat_1(sK2) = k2_relset_1(k2_struct_0(sK0),k2_struct_0(sK1),sK2) | ~spl3_16),
% 0.21/0.44    inference(resolution,[],[f136,f44])).
% 0.21/0.44  fof(f137,plain,(
% 0.21/0.44    spl3_16 | ~spl3_5 | ~spl3_13 | ~spl3_14),
% 0.21/0.44    inference(avatar_split_clause,[],[f132,f120,f114,f72,f134])).
% 0.21/0.44  fof(f72,plain,(
% 0.21/0.44    spl3_5 <=> m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_5])])).
% 0.21/0.44  fof(f132,plain,(
% 0.21/0.44    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(k2_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_5 | ~spl3_13 | ~spl3_14)),
% 0.21/0.44    inference(forward_demodulation,[],[f131,f122])).
% 0.21/0.44  fof(f131,plain,(
% 0.21/0.44    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),k2_struct_0(sK1)))) | (~spl3_5 | ~spl3_13)),
% 0.21/0.44    inference(forward_demodulation,[],[f74,f116])).
% 0.21/0.44  fof(f74,plain,(
% 0.21/0.44    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) | ~spl3_5),
% 0.21/0.44    inference(avatar_component_clause,[],[f72])).
% 0.21/0.44  fof(f130,plain,(
% 0.21/0.44    spl3_15 | ~spl3_6 | ~spl3_13 | ~spl3_14),
% 0.21/0.44    inference(avatar_split_clause,[],[f125,f120,f114,f77,f127])).
% 0.21/0.44  fof(f77,plain,(
% 0.21/0.44    spl3_6 <=> v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_6])])).
% 0.21/0.44  fof(f125,plain,(
% 0.21/0.44    v1_funct_2(sK2,k2_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_6 | ~spl3_13 | ~spl3_14)),
% 0.21/0.44    inference(forward_demodulation,[],[f124,f122])).
% 0.21/0.44  fof(f124,plain,(
% 0.21/0.44    v1_funct_2(sK2,u1_struct_0(sK0),k2_struct_0(sK1)) | (~spl3_6 | ~spl3_13)),
% 0.21/0.44    inference(forward_demodulation,[],[f79,f116])).
% 0.21/0.44  fof(f79,plain,(
% 0.21/0.44    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) | ~spl3_6),
% 0.21/0.44    inference(avatar_component_clause,[],[f77])).
% 0.21/0.44  fof(f123,plain,(
% 0.21/0.44    spl3_14 | ~spl3_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f118,f92,f120])).
% 0.21/0.44  fof(f92,plain,(
% 0.21/0.44    spl3_9 <=> l1_struct_0(sK0)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_9])])).
% 0.21/0.44  fof(f118,plain,(
% 0.21/0.44    u1_struct_0(sK0) = k2_struct_0(sK0) | ~spl3_9),
% 0.21/0.44    inference(resolution,[],[f94,f39])).
% 0.21/0.44  fof(f39,plain,(
% 0.21/0.44    ( ! [X0] : (~l1_struct_0(X0) | k2_struct_0(X0) = u1_struct_0(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f14])).
% 0.21/0.44  fof(f14,plain,(
% 0.21/0.44    ! [X0] : (k2_struct_0(X0) = u1_struct_0(X0) | ~l1_struct_0(X0))),
% 0.21/0.44    inference(ennf_transformation,[],[f8])).
% 0.21/0.44  fof(f8,axiom,(
% 0.21/0.44    ! [X0] : (l1_struct_0(X0) => k2_struct_0(X0) = u1_struct_0(X0))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_struct_0)).
% 0.21/0.44  fof(f94,plain,(
% 0.21/0.44    l1_struct_0(sK0) | ~spl3_9),
% 0.21/0.44    inference(avatar_component_clause,[],[f92])).
% 0.21/0.44  fof(f117,plain,(
% 0.21/0.44    spl3_13 | ~spl3_8),
% 0.21/0.44    inference(avatar_split_clause,[],[f112,f87,f114])).
% 0.21/0.44  fof(f87,plain,(
% 0.21/0.44    spl3_8 <=> l1_struct_0(sK1)),
% 0.21/0.44    introduced(avatar_definition,[new_symbols(naming,[spl3_8])])).
% 0.21/0.44  fof(f112,plain,(
% 0.21/0.44    u1_struct_0(sK1) = k2_struct_0(sK1) | ~spl3_8),
% 0.21/0.44    inference(resolution,[],[f89,f39])).
% 0.21/0.44  fof(f89,plain,(
% 0.21/0.44    l1_struct_0(sK1) | ~spl3_8),
% 0.21/0.44    inference(avatar_component_clause,[],[f87])).
% 0.21/0.44  fof(f111,plain,(
% 0.21/0.44    ~spl3_10 | ~spl3_7 | spl3_12 | ~spl3_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f97,f62,f108,f82,f99])).
% 0.21/0.44  fof(f97,plain,(
% 0.21/0.44    k5_relat_1(k2_funct_1(sK2),sK2) = k6_relat_1(k2_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_3),
% 0.21/0.44    inference(resolution,[],[f64,f41])).
% 0.21/0.44  fof(f41,plain,(
% 0.21/0.44    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f16,plain,(
% 0.21/0.44    ! [X0] : ((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0) | ~v1_funct_1(X0) | ~v1_relat_1(X0))),
% 0.21/0.44    inference(flattening,[],[f15])).
% 0.21/0.44  fof(f15,plain,(
% 0.21/0.44    ! [X0] : (((k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0))) | ~v2_funct_1(X0)) | (~v1_funct_1(X0) | ~v1_relat_1(X0)))),
% 0.21/0.44    inference(ennf_transformation,[],[f1])).
% 0.21/0.44  fof(f1,axiom,(
% 0.21/0.44    ! [X0] : ((v1_funct_1(X0) & v1_relat_1(X0)) => (v2_funct_1(X0) => (k5_relat_1(k2_funct_1(X0),X0) = k6_relat_1(k2_relat_1(X0)) & k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)))))),
% 0.21/0.44    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t61_funct_1)).
% 0.21/0.44  fof(f64,plain,(
% 0.21/0.44    v2_funct_1(sK2) | ~spl3_3),
% 0.21/0.44    inference(avatar_component_clause,[],[f62])).
% 0.21/0.44  fof(f106,plain,(
% 0.21/0.44    ~spl3_10 | ~spl3_7 | spl3_11 | ~spl3_3),
% 0.21/0.44    inference(avatar_split_clause,[],[f96,f62,f103,f82,f99])).
% 0.21/0.44  fof(f96,plain,(
% 0.21/0.44    k5_relat_1(sK2,k2_funct_1(sK2)) = k6_relat_1(k1_relat_1(sK2)) | ~v1_funct_1(sK2) | ~v1_relat_1(sK2) | ~spl3_3),
% 0.21/0.44    inference(resolution,[],[f64,f40])).
% 0.21/0.44  fof(f40,plain,(
% 0.21/0.44    ( ! [X0] : (~v2_funct_1(X0) | k5_relat_1(X0,k2_funct_1(X0)) = k6_relat_1(k1_relat_1(X0)) | ~v1_funct_1(X0) | ~v1_relat_1(X0)) )),
% 0.21/0.44    inference(cnf_transformation,[],[f16])).
% 0.21/0.44  fof(f95,plain,(
% 0.21/0.44    spl3_9),
% 0.21/0.44    inference(avatar_split_clause,[],[f30,f92])).
% 0.21/0.44  fof(f30,plain,(
% 0.21/0.44    l1_struct_0(sK0)),
% 0.21/0.44    inference(cnf_transformation,[],[f29])).
% 0.21/0.45  fof(f29,plain,(
% 0.21/0.45    (((k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2)) & l1_struct_0(sK1)) & l1_struct_0(sK0)),
% 0.21/0.45    inference(skolemisation,[status(esa),new_symbols(skolem,[sK0,sK1,sK2])],[f13,f28,f27,f26])).
% 0.21/0.45  fof(f26,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : ((k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0)) => (? [X1] : (? [X2] : ((k1_partfun1(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(sK0))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f27,plain,(
% 0.21/0.45    ? [X1] : (? [X2] : ((k1_partfun1(u1_struct_0(X1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(X1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(sK0),X2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_struct_0(X1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(X1),X2) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) => (? [X2] : ((k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),X2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) & l1_struct_0(sK1))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f28,plain,(
% 0.21/0.45    ? [X2] : ((k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),X2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),X2) = k2_struct_0(sK1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(X2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(X2)) => ((k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))) & v2_funct_1(sK2) & k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2) & m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1)))) & v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1)) & v1_funct_1(sK2))),
% 0.21/0.45    introduced(choice_axiom,[])).
% 0.21/0.45  fof(f13,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : ((k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1) & m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.45    inference(flattening,[],[f12])).
% 0.21/0.45  fof(f12,plain,(
% 0.21/0.45    ? [X0] : (? [X1] : (? [X2] : (((k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) != k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) | k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) != k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2))) & (v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1))) & (m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2))) & l1_struct_0(X1)) & l1_struct_0(X0))),
% 0.21/0.45    inference(ennf_transformation,[],[f11])).
% 0.21/0.45  fof(f11,negated_conjecture,(
% 0.21/0.45    ~! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) = k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) & k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.21/0.45    inference(negated_conjecture,[],[f10])).
% 0.21/0.45  fof(f10,conjecture,(
% 0.21/0.45    ! [X0] : (l1_struct_0(X0) => ! [X1] : (l1_struct_0(X1) => ! [X2] : ((m1_subset_1(X2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(X0),u1_struct_0(X1)))) & v1_funct_2(X2,u1_struct_0(X0),u1_struct_0(X1)) & v1_funct_1(X2)) => ((v2_funct_1(X2) & k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2) = k2_struct_0(X1)) => (k1_partfun1(u1_struct_0(X1),u1_struct_0(X0),u1_struct_0(X0),u1_struct_0(X1),k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2),X2) = k6_partfun1(k2_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)) & k1_partfun1(u1_struct_0(X0),u1_struct_0(X1),u1_struct_0(X1),u1_struct_0(X0),X2,k2_tops_2(u1_struct_0(X0),u1_struct_0(X1),X2)) = k6_partfun1(k1_relset_1(u1_struct_0(X0),u1_struct_0(X1),X2)))))))),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_tops_2)).
% 0.21/0.45  fof(f90,plain,(
% 0.21/0.45    spl3_8),
% 0.21/0.45    inference(avatar_split_clause,[],[f31,f87])).
% 0.21/0.45  fof(f31,plain,(
% 0.21/0.45    l1_struct_0(sK1)),
% 0.21/0.45    inference(cnf_transformation,[],[f29])).
% 0.21/0.45  fof(f85,plain,(
% 0.21/0.45    spl3_7),
% 0.21/0.45    inference(avatar_split_clause,[],[f32,f82])).
% 0.21/0.45  fof(f32,plain,(
% 0.21/0.45    v1_funct_1(sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f29])).
% 0.21/0.45  fof(f80,plain,(
% 0.21/0.45    spl3_6),
% 0.21/0.45    inference(avatar_split_clause,[],[f33,f77])).
% 0.21/0.45  fof(f33,plain,(
% 0.21/0.45    v1_funct_2(sK2,u1_struct_0(sK0),u1_struct_0(sK1))),
% 0.21/0.45    inference(cnf_transformation,[],[f29])).
% 0.21/0.45  fof(f75,plain,(
% 0.21/0.45    spl3_5),
% 0.21/0.45    inference(avatar_split_clause,[],[f34,f72])).
% 0.21/0.45  fof(f34,plain,(
% 0.21/0.45    m1_subset_1(sK2,k1_zfmisc_1(k2_zfmisc_1(u1_struct_0(sK0),u1_struct_0(sK1))))),
% 0.21/0.45    inference(cnf_transformation,[],[f29])).
% 0.21/0.45  fof(f70,plain,(
% 0.21/0.45    spl3_4),
% 0.21/0.45    inference(avatar_split_clause,[],[f35,f67])).
% 0.21/0.45  fof(f35,plain,(
% 0.21/0.45    k2_struct_0(sK1) = k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f29])).
% 0.21/0.45  fof(f65,plain,(
% 0.21/0.45    spl3_3),
% 0.21/0.45    inference(avatar_split_clause,[],[f36,f62])).
% 0.21/0.45  fof(f36,plain,(
% 0.21/0.45    v2_funct_1(sK2)),
% 0.21/0.45    inference(cnf_transformation,[],[f29])).
% 0.21/0.45  fof(f60,plain,(
% 0.21/0.45    ~spl3_1 | ~spl3_2),
% 0.21/0.45    inference(avatar_split_clause,[],[f51,f57,f53])).
% 0.21/0.45  fof(f53,plain,(
% 0.21/0.45    spl3_1 <=> k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) = k6_relat_1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_1])])).
% 0.21/0.45  fof(f57,plain,(
% 0.21/0.45    spl3_2 <=> k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) = k6_relat_1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.45    introduced(avatar_definition,[new_symbols(naming,[spl3_2])])).
% 0.21/0.45  fof(f51,plain,(
% 0.21/0.45    k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_relat_1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_relat_1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.45    inference(forward_demodulation,[],[f50,f38])).
% 0.21/0.45  fof(f38,plain,(
% 0.21/0.45    ( ! [X0] : (k6_partfun1(X0) = k6_relat_1(X0)) )),
% 0.21/0.45    inference(cnf_transformation,[],[f6])).
% 0.21/0.45  fof(f6,axiom,(
% 0.21/0.45    ! [X0] : k6_partfun1(X0) = k6_relat_1(X0)),
% 0.21/0.45    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',redefinition_k6_partfun1)).
% 0.21/0.45  fof(f50,plain,(
% 0.21/0.45    k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_relat_1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.45    inference(forward_demodulation,[],[f37,f38])).
% 0.21/0.45  fof(f37,plain,(
% 0.21/0.45    k1_partfun1(u1_struct_0(sK1),u1_struct_0(sK0),u1_struct_0(sK0),u1_struct_0(sK1),k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2),sK2) != k6_partfun1(k2_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) | k1_partfun1(u1_struct_0(sK0),u1_struct_0(sK1),u1_struct_0(sK1),u1_struct_0(sK0),sK2,k2_tops_2(u1_struct_0(sK0),u1_struct_0(sK1),sK2)) != k6_partfun1(k1_relset_1(u1_struct_0(sK0),u1_struct_0(sK1),sK2))),
% 0.21/0.45    inference(cnf_transformation,[],[f29])).
% 0.21/0.45  % SZS output end Proof for theBenchmark
% 0.21/0.45  % (16205)------------------------------
% 0.21/0.45  % (16205)Version: Vampire 4.5.0 (commit 2ee491ce on 2020-06-19 13:55:12 +0100)
% 0.21/0.45  % (16205)Termination reason: Refutation
% 0.21/0.45  
% 0.21/0.45  % (16205)Memory used [KB]: 11001
% 0.21/0.45  % (16205)Time elapsed: 0.014 s
% 0.21/0.45  % (16205)------------------------------
% 0.21/0.45  % (16205)------------------------------
% 0.21/0.45  % (16193)Success in time 0.088 s
%------------------------------------------------------------------------------
